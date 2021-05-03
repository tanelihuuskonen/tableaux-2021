module SCIRS (SCINode(..), sciIsProvable, FormulaLists(..), startNode) where
import Data.List(nub, union)
import SCITypes (SCIFormula(..), SCIModel(..), SCIAssignment(..), sciShorten)
import RSProof (rsIsProof, rsProof, RSSystem(..), RSTree(..))
import SCIHelper (UnOp)
import qualified Data.Map.Strict as M

data FormulaLists = FL { newF, idF, oldF :: [SCIFormula] }
    deriving (Eq, Show)

data SCINode =
    SCINormalNode {
        pos, neg :: FormulaLists,
        nNodes :: Int } -- # of theoretical nodes collapsed into one
    | SCIAxNegationNode {
        ax :: SCIFormula,
        pos, neg :: FormulaLists }
    | SCIAxIdentityNode {
        ax :: SCIFormula,
        pos, neg :: FormulaLists }
    | SCIExhaustedNode {
        pos, neg :: FormulaLists }
    deriving (Eq, Show)

instance RSSystem SCINode where
    rsSuccessors = sciRSSuccessors
    rsIsAxiomatic = sciIsAxiomatic
    rsIsProven = sciIsAxiomatic
    rsIsRefuted = sciIsRefuted
    rsTreeDepth = sciTreeDepth
    rsTreeSize = sciTreeSize

emptyFL = FL [] [] []
flNew f = FL [f] [] []
flId f = FL [] [f] []
flOld f = FL [] [] [f]

type SCIRule = SCIFormula -> [SCINode]

sciPosRule :: SCIRule
sciPosRule v@(Variable _) = [SCINormalNode (flOld v) emptyFL 1]
sciPosRule (Not f) = jointNew [] [f]
sciPosRule (And f g) = splitNew [f, g]
sciPosRule (Or f g) = jointNew [f, g] []
sciPosRule (Imply f g) = jointNew [g] [f]
sciPosRule (Equiv f g) = splitNew [Imply f g, Imply g f]
sciPosRule eqn@(Ident f g)
    | f == g = [SCIAxIdentityNode eqn (flId eqn) emptyFL]
    | otherwise = [SCINormalNode (flId eqn) emptyFL 1]

sciNegRule v@(Variable _) = [SCINormalNode emptyFL (flOld v) 1]
sciNegRule (Not f) = jointNew [f] []
sciNegRule (And f g) = jointNew [] [f, g]
sciNegRule (Or f g) = splitNew [Not f, Not g]
sciNegRule (Imply f g) = splitNew [f, Not g]
sciNegRule (Equiv f g) = jointNew [] [Imply f g, Imply g f]
sciNegRule eqn@(Ident f g)
    | f == g = [SCINormalNode emptyFL emptyFL 1]
    | otherwise = [SCINormalNode emptyFL (FL [Equiv f g] [eqn] []) 1]

jointNew :: [SCIFormula] -> [SCIFormula] -> [SCINode]
jointNew p n = [SCINormalNode (FL p [] []) (FL n [] []) 1]

splitNew :: [SCIFormula] -> [SCINode]
splitNew = map sn where
    sn (Not f) = SCINormalNode emptyFL (flNew f) 1
    sn f = SCINormalNode (flNew f) emptyFL 1

sciIsProvable :: SCIFormula -> Bool
sciIsProvable = rsIsProof . rsProof . startNode

startNode :: SCIFormula -> SCINode
startNode f = SCINormalNode (flNew f) emptyFL 1

sciIsAxiomatic :: SCINode -> Bool
sciIsAxiomatic SCIAxNegationNode{} = True
sciIsAxiomatic SCIAxIdentityNode{} = True
sciIsAxiomatic _ = False

sciIsRefuted SCIExhaustedNode{} = True
sciIsRefuted _ = False

sciTreeSize (RSLeaf SCIAxNegationNode{}) = 1
sciTreeSize (RSLeaf SCIAxIdentityNode{}) = 1
sciTreeSize (RSLeaf SCIExhaustedNode{}) = 1
sciTreeSize (RSLeaf n@(SCINormalNode _ _ s)) = s
sciTreeSize (RSUnary (SCINormalNode _ _ s) l) = s + sciTreeSize l
sciTreeSize (RSBinary (SCINormalNode _ _ s) l r)
    = s + sciTreeSize l + sciTreeSize r

sciTreeDepth (RSLeaf SCIAxNegationNode{}) = 1
sciTreeDepth (RSLeaf SCIAxIdentityNode{}) = 1
sciTreeDepth (RSLeaf SCIExhaustedNode{}) = 1
sciTreeDepth (RSLeaf n@(SCINormalNode _ _ s)) = s
sciTreeDepth (RSUnary (SCINormalNode _ _ s) l) = s + sciTreeDepth l
sciTreeDepth (RSBinary (SCINormalNode _ _ s) l r)
    = s + max (sciTreeDepth l) (sciTreeDepth r)

sciRSSuccessors :: SCINode -> [SCINode]
sciRSSuccessors SCIAxNegationNode{} = []
sciRSSuccessors SCIAxIdentityNode{} = []
sciRSSuccessors SCIExhaustedNode{} = []
sciRSSuccessors (SCINormalNode p@(FL (f:fs) i o) n _)
    | elemFL f n = [SCIAxNegationNode f p n]
    | otherwise = applyRule (sciPosRule f) (SCINormalNode (FL fs i o) n 1)
sciRSSuccessors (SCINormalNode p n@(FL (f:fs) i o) _)
    | elemFL f p = [SCIAxNegationNode f p n]
    | otherwise = applyRule (sciNegRule f) (SCINormalNode p (FL fs i o) 1)
sciRSSuccessors (SCINormalNode p@(FL [] pi po) n@(FL [] ni no) _)
        | null pi || null ni = [SCIExhaustedNode p n]
        | containsAx pi = [SCIAxIdentityNode ax p n]
        | (ni == xni) && (pi == xpi) = [SCIExhaustedNode p n]
        | otherwise = [SCINormalNode xp xn nn]
    where
        xpi = expandIds pi ni
        xni = expandIds ni ni
        ax = getAx pi
        xp = p{idF = xpi}
        xn = n{idF = xni}
        nn = length (newIds pi ni) + length (newIds ni ni)

applyRule :: [SCINode] -> SCINode -> [SCINode]
applyRule ns base = map (unionNode base) ns

unionNode :: SCINode -> SCINode -> SCINode
unionNode (SCINormalNode bp bn _) (SCINormalNode p n _)
    = SCINormalNode (unionFL bp p) (unionFL bn n) 1
unionNode (SCINormalNode bp bn _) (SCIAxIdentityNode a p n)
    = SCIAxIdentityNode a (unionFL bp p) (unionFL bn n)
unionNode (SCINormalNode bp bn _) (SCIAxNegationNode a p n)
    = SCIAxNegationNode a (unionFL bp p) (unionFL bn n)

elemFL :: SCIFormula -> FormulaLists -> Bool
elemFL f (FL n i o) = elem f n || elem f i || elem f o

unionFL :: FormulaLists -> FormulaLists -> FormulaLists
unionFL (FL n1 i1 o1) (FL n2 i2 o2)
    = FL (n1 `union` n2) (i1 `union` i2) (o1 `union` o2)

newIds :: [SCIFormula] -> [SCIFormula] -> [SCIFormula]
newIds a o = filter (`notElem` a) (expandIds a o)

expandIds :: [SCIFormula] -> [SCIFormula] -> [SCIFormula]
-- expandIds args ops

expandIds = foldr expId

expId :: SCIFormula -> [SCIFormula] -> [SCIFormula]
expId (Ident f g) l = union l $ filter isIdent $ map (sciShorten f g) l


containsAx :: [SCIFormula] -> Bool
containsAx = any isAx

isAx :: SCIFormula -> Bool
isAx (Ident f g) = f == g
isAx _ = False

isIdent :: SCIFormula -> Bool
isIdent (Ident _ _) = True
isIdent _ = False

getAx :: [SCIFormula] -> SCIFormula
getAx = head . filter isAx

-- foldFL :: FormulaLists -> [SCIFormula] -> [SCIFormula]
-- foldFL (FL n i o) fs = foldr1 union [n, i, o, fs]

addId :: SCIFormula -> SCIFormula -> [SCIFormula] -> [SCIFormula]
addId f g = addFuncUniq $ sciShorten f g

addFuncUniq :: UnOp SCIFormula -> [SCIFormula] -> [SCIFormula]
addFuncUniq f xs = filter (`notElem` xs) (nub $ map f xs)

type SCIMap = M.Map SCIFormula SCIFormula

lup :: SCIMap -> SCIFormula -> SCIFormula
lup m f = M.findWithDefault f f m

sciEqsToMap :: [SCIFormula] -> SCIMap
sciEqsToMap [] = M.empty

sciCounterModel :: FormulaLists -> SCIModel SCIFormula
sciCounterModel = undefined

sciCounterAssignment :: FormulaLists -> SCIAssignment SCIFormula
sciCounterAssignment fs s = lup (sciEqsToMap $ idF fs) (Variable s)

sciCounterExample :: FormulaLists ->
        (SCIModel SCIFormula, SCIAssignment SCIFormula)
sciCounterExample fs = (sciCounterModel fs, sciCounterAssignment fs)

module Main where
import System.Environment (getArgs, getProgName)
import SCITypes (trapError, sciSubst, SCIFormula(..), SCIError(..))
import SCIParse (readFormula)

isVar :: SCIFormula -> Bool
isVar (Variable _) = True
isVar _ = False

isLiteral :: SCIFormula -> Bool
isLiteral (Not x) = isVar x
isLiteral x = isVar x

isSimple :: SCIFormula -> Bool
isSimple (Imply (Variable _) (Variable _)) = True
isSimple (Ident (Variable _) (Variable _)) = True
isSimple x = isLiteral x

isIdentity :: SCIFormula -> Bool
isIdentity (Ident _ _) = True
isIdentity _ = False

isPMIdent :: SCIFormula -> Bool
isPMIdent (Not x) = isIdentity x
isPMIdent x = isIdentity x

isAtomicIdent :: SCIFormula -> Bool
isAtomicIdent (Ident x y) = (isVar x && isSimple y) || (isSimple x && isVar y)
isAtomicIdent _ = False

isAtIdOrSimple :: SCIFormula -> Bool
isAtIdOrSimple x = isSimple x || isAtomicIdent x

trVar :: SCIFormula -> SCIFormula
trVar f@(Variable (c:cs))
    | c == 'v' = Variable (c:c:cs)
    | otherwise = f
trVar (Not x) = Not $ trVar x
trVar (And x y) = And (trVar x) (trVar y)
trVar (Or x y) = Or (trVar x) (trVar y)
trVar (Imply x y) = Imply (trVar x) (trVar y)
trVar (Equiv x y) = Equiv (trVar x) (trVar y)
trVar (Ident x y) = Ident (trVar x) (trVar y)

varNew :: String -> SCIFormula
varNew s = Variable $ "v" ++ s

trStr :: String -> SCIFormula -> [SCIFormula]
trStr s x | isSimple x = [Ident (varNew s) x]
trStr s (Not x) = trStr (s ++ "0") x ++  [Ident (varNew s) $ Not $ varNew $ s ++ "0"]
trStr s (And x y) = trStr (s ++ "0") x ++ trStr (s ++ "1") y ++ [Ident (varNew s) $ And (varNew $ s ++ "0") (varNew $ s ++ "1")]
trStr s (Or x y) = trStr (s ++ "0") x ++ trStr (s ++ "1") y ++ [Ident (varNew s) $ Or (varNew $ s ++ "0") (varNew $ s ++ "1")]
trStr s (Imply x y) = trStr (s ++ "0") x ++ trStr (s ++ "1") y ++ [Ident (varNew s) $ Imply (varNew $ s ++ "0") (varNew $ s ++ "1")]
trStr s (Equiv x y) = trStr (s ++ "0") x ++ trStr (s ++ "1") y ++ [Ident (varNew s) $ Equiv (varNew $ s ++ "0") (varNew $ s ++ "1")]
trStr s (Ident x y) = trStr (s ++ "0") x ++ trStr (s ++ "1") y ++ [Ident (varNew s) $ Ident (varNew $ s ++ "0") (varNew $ s ++ "1")]

translateSCI :: SCIFormula -> SCIFormula
translateSCI x | isAtIdOrSimple x = x
translateSCI x = foldr Imply (varNew "") (trStr "" $ trVar x)

main :: IO ()
main = do
    argline <- getArgs
    input <- if not $ null argline
        then return $ head argline
        else getLine
    let f = readFormula input
    case readFormula input of
        Left x -> putStrLn $ "Input error: " ++ show x
        Right x -> print $ translateSCI x

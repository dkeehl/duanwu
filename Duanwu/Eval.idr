module Duanwu.Eval

import Duanwu.LispVal
import Data.SortedMap
import Control.ST
import Control.ST.Exception

mapM : Monad m => (a -> m b) -> List a -> m (List b)
mapM _ [] = pure []
mapM f (x :: xs) = do x' <- f x
                      xs' <- mapM f xs
                      pure $ x' :: xs'

interface Convert ty where
  conv : LispVal -> Either LispError ty

Convert Integer where
  conv (LispNum n) = Right n
  conv (LispStr str)
      = if all isDigit (unpack str)
           then Right $ cast str
           else Left $ TypeMisMatch "number" (LispStr str)
  conv (LispList [n]) = conv n
  conv notNum = Left $ TypeMisMatch "number" notNum 

Convert String where
  conv (LispNum x) = Right (show x)
  conv (LispStr x) = Right x
  conv val@(LispBool _) = Right (show val)
  conv notString = Left $ TypeMisMatch "string" notString

Convert Bool where
  conv (LispBool b) = Right b
  conv notBool = Left $ TypeMisMatch "boolean" notBool

numericBinop : (Integer -> Integer -> Integer) ->
               List LispVal -> Either LispError LispVal
numericBinop op [] = Left $ NumArgs 2 []
numericBinop op params = do nums <- mapM conv params
                            pure $ LispNum (foldl1 op nums)

boolBinop : Convert a => (a -> a -> Bool) -> List LispVal ->
                         Either LispError LispVal
boolBinop op [x, y] = do x' <- conv x
                         y' <- conv y
                         pure $ LispBool (op x' y')
boolBinop _ args = Left $ NumArgs 2 args

car : List LispVal -> Either LispError LispVal
car [LispList (x :: xs)] = Right x
car [LispDotted (x :: xs) _] = Right x
car [badArg] = Left $ TypeMisMatch "pair" badArg
car badArgList = Left $ NumArgs 1 badArgList

cdr : List LispVal -> Either LispError LispVal
cdr [LispList [_]] = Right $ LispNil
cdr [LispList (_ :: xs)] = Right $ LispList xs
cdr [LispDotted [_] x] = Right x
cdr [LispDotted (_ :: xs) x] = Right $ LispDotted xs x
cdr [badArg] = Left $ TypeMisMatch "pair" badArg
cdr badArgList = Left $ NumArgs 1 badArgList

cons : List LispVal -> Either LispError LispVal
cons [x, LispNil] = Right $ LispList [x]
cons [x, LispList xs] = Right $ LispList (x :: xs)
cons [x, LispDotted xs xlast] = Right $ LispDotted (x :: xs) xlast
cons [x, y] = Right $ LispDotted [x] y
cons badArgList = Left $ NumArgs 2 badArgList

eqv : List LispVal -> Either LispError LispVal
eqv [LispBool b1, LispBool b2] = Right $ LispBool (b1 == b2)
eqv [LispNum n1, LispNum n2] = Right $ LispBool (n1 == n2)
eqv [LispStr s1, LispStr s2] = Right $ LispBool (s1 == s2)
eqv [LispAtom a1, LispAtom a2] = Right $ LispBool (a1 == a2)
eqv [LispNil, LispNil] = Right $ LispBool True
eqv [LispList [], LispList []] = Right $ LispBool True
eqv [LispList [], LispList _] = Right $ LispBool False
eqv [LispList _, LispList []] = Right $ LispBool False
eqv [LispList (x :: xs), LispList (y :: ys)]
    = do LispBool True <- eqv [x, y] | _ => pure (LispBool False)
         eqv [LispList xs, LispList ys]
eqv [LispDotted xs x, LispDotted ys y]
    = eqv [LispList (xs ++ [x]), LispList (ys ++ [y])]
eqv [_, _] = Right $ LispBool False
eqv badArgList = Left $ NumArgs 2 badArgList

primitives : List (String,  List LispVal -> Either LispError LispVal)
primitives = [("+", numericBinop (+)),
              ("-", numericBinop (-)),
              ("*", numericBinop (*)),
              ("/", numericBinop div),
              ("quotient", numericBinop div),
              ("remainder", numericBinop mod),
              ("car", car),
              ("cdr", cdr),
              ("cons", cons),
              ("eq?", eqv),
              ("eqv?", eqv),
              ("=", boolBinop $ (==) {ty = Integer}),
              ("<", boolBinop $ (<) {ty = Integer}),
              (">", boolBinop $ (>) {ty = Integer}),
              ("/=", boolBinop $ (/=) {ty = Integer}),
              (">=", boolBinop $ (>=) {ty = Integer}),
              ("<=", boolBinop $ (<=) {ty = Integer}),
              ("&&", boolBinop (\x, y => x && y)),
              ("||", boolBinop (\x, y => x || y)),
              ("string=?", boolBinop $ (==) {ty = String}),
              ("string<?", boolBinop $ (<) {ty = String}),
              ("string>?", boolBinop $ (>) {ty = String}),
              ("string<=?", boolBinop $ (<=) {ty = String}),
              ("string>=?", boolBinop $ (>=) {ty = String})]

apply : String -> List LispVal -> Either LispError LispVal
apply fname args
    = case lookup fname primitives of
           Nothing =>
             Left $ NotFunction "Unrecognized primitive function args" fname
           Just f => f args

mapST : (a -> STrans m b st (const st)) -> List a ->
        STrans m (List b) st (const st)
mapST f [] = pure []
mapST f (x :: xs) = do x' <- f x
                       xs' <- mapST f xs
                       pure (x' :: xs')

liftEither : Exception m e => Either e a -> STrans m a res (const res)
liftEither (Left err) = throw err
liftEither (Right val) = pure val

public export
EnvCtx : Type
EnvCtx = SortedMap String LispVal

updateVar : (env : Var) -> (k : String) -> (v : LispVal) ->
            ST m LispVal [env ::: State EnvCtx]
updateVar env k v = update env (insert k v) >>= pure v

export
eval : Exception m LispError => (env : Var) -> LispVal ->
       ST m LispVal [env ::: State EnvCtx]
eval env val@(LispStr _) = pure val
eval env val@(LispNum _) = pure val
eval env val@(LispBool _) = pure val
eval env LispNil = pure LispNil
eval env (LispList [LispAtom "quote", val]) = pure val
eval env (LispList [LispAtom "if", pred, conseq, alt])
  = do LispBool False <- eval env pred | _ => eval env conseq
       eval env alt
eval env (LispList [LispAtom "define", LispAtom var, form])
  = updateVar env var !(eval env form)
eval env (LispList [LispAtom "set!", LispAtom var, form])
  = do e <- read env 
       case lookup var e of
            Nothing => throw (UnboundVar "Setting an unbound variable" var)
            Just _ => updateVar env var !(eval env form)
eval env (LispList (LispAtom fn :: args))
  = do args' <- mapST (eval env) args
       liftEither (apply fn args') 

eval env val = throw $ Default ("unmatched case " ++ show val)

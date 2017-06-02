module Duanwu.Eval

import LispVal
import Parser
--import Control.Catchable

mapM : Monad m => (a -> m b) -> List a -> m (List b)
mapM _ [] = pure []
mapM f (x :: xs) = do x' <- f x
                      xs' <- mapM f xs
                      pure $ x' :: xs'

unpackNum : LispVal -> Either LispError Integer
unpackNum (LispNum n) = Right n
unpackNum (LispStr str) = if all isDigit (unpack str)
                             then Right $ cast str
                             else Left $ TypeMisMatch "number" (LispStr str)
unpackNum (LispList [n]) = unpackNum n
unpackNum notNum = Left $ TypeMisMatch "number" notNum 

numericBinop : (Integer -> Integer -> Integer) ->
               List LispVal -> Either LispError LispVal
numericBinop op [] = Left $ NumArgs 2 []
numericBinop op params = do nums <- mapM unpackNum params
                            pure $ LispNum (foldl1 op nums)

primitives : List (String,  List LispVal -> Either LispError LispVal)
primitives = [("+", numericBinop (+)),
              ("-", numericBinop (-)),
              ("*", numericBinop (*)),
              ("/", numericBinop div),
              ("quotient", numericBinop div),
              ("remainder", numericBinop mod)]

apply : String -> List LispVal -> Either LispError LispVal
apply fname args
    = case lookup fname primitives of
           Nothing =>
             Left $ NotFunction "Unrecognized primitive function args" fname
           Just f => f args

export
eval : LispVal -> Either LispError LispVal
eval val@(LispStr _) = pure val
eval val@(LispNum _) = pure val
eval val@(LispBool _) = pure val
eval LispNil = pure LispNil
eval (LispList [LispAtom "quote", val]) = pure val
eval (LispList (LispAtom fn :: args)) = mapM eval args >>= apply fn

eval val = Left $ Default ("unmatched case " ++ show val)

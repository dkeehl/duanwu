module Duanwu.Eval

import LispVal
import Parser
--import Control.ST
--import Control.ST.Exception

unpackNum : LispVal -> Integer
unpackNum (LispNum n) = n
unpackNum (LispStr n) = cast n
unpackNum (LispList [n]) = unpackNum n
unpackNum _ = 0

numericBinop : (Integer -> Integer -> Integer) -> List LispVal -> LispVal
numericBinop op params = LispNum $ foldl1 op $ map unpackNum params

primitives : List (String,  List LispVal -> LispVal)
primitives = [("+", numericBinop (+)),
              ("-", numericBinop (-)),
              ("*", numericBinop (*)),
              ("/", numericBinop div),
              ("quotient", numericBinop div),
              ("remainder", numericBinop mod)]

apply : String -> List LispVal -> LispVal
apply fname args = case lookup fname primitives of
                        Nothing => LispBool False
                        Just f => f args

export
eval : LispVal -> LispVal
eval val@(LispStr _) = val
eval val@(LispNum _) = val
eval val@(LispBool _) = val
eval LispNil = LispNil
eval (LispList [LispAtom "quote", val]) = val
eval (LispList (LispAtom fn :: args)) = apply fn $ map eval args

eval val = LispStr $ "unmatched case " ++ show val

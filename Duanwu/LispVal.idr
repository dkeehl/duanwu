module Duanwu.LispVal

public export
data LispVal = LispAtom String
             | LispNum Integer
             | LispStr String
             | LispBool Bool
             | LispNil
             | LispList (List LispVal)
             | LispDotted (List LispVal) LispVal

public export
EnvCtx : Type
EnvCtx = List (String, LispVal)

export
Show LispVal where
  show (LispAtom atom) = atom
  show (LispNum n) = show n
  show (LispStr str) = "\"" ++ str ++ "\""
  show (LispBool True) = "#t"
  show (LispBool False) = "#f"
  show LispNil = "Nil"
  show (LispList contents) = "(" ++ (unwords $ map show contents) ++ ")"
  show (LispDotted contents val)
      = "(" ++ (unwords $ map show contents) ++ " . " ++ show val ++ ")"

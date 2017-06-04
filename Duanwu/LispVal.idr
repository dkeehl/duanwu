module Duanwu.LispVal

%access export

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

public export
data LispError : Type where
     NumArgs : (expected : Integer) -> (found : List LispVal) -> LispError
     TypeMisMatch : (expected : String) -> (found : LispVal) -> LispError
     Parser : (err : String) -> LispError
     BadSpecialForm : (msg : String) -> (form : LispVal) -> LispError
     NotFunction : (msg : String) -> (fname : String) -> LispError
     UnboundVar : (msg : String) -> (varname : String) -> LispError
     Default : String -> LispError

private
unwordsList : List LispVal -> String
unwordsList = unwords . map show

Show LispError where
  show (NumArgs expected found) = "Expected " ++ show expected ++
                                " args; found values " ++ unwordsList found
  show (TypeMisMatch expected found) = "Invalid type: expected " ++
                                       expected ++ ", found " ++ show found
  show (Parser err) = "Parser error at " ++ err
  show (BadSpecialForm msg form) = msg ++ ": " ++ show form
  show (NotFunction msg fname) = msg ++ ": " ++ fname
  show (UnboundVar msg varname) = msg ++ ": " ++ varname
  show (Default msg) = msg


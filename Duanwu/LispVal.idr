module Duanwu.LispVal

import Data.IORef

%access public export

mutual
  data LispVal : Type where
       LispAtom : String -> LispVal
       LispNum : Integer -> LispVal
       LispStr : String -> LispVal
       LispBool : Bool -> LispVal
       LispNil : LispVal
       LispList : List LispVal -> LispVal
       LispDotted : List LispVal -> LispVal -> LispVal
       Function : (fn : List LispVal -> Either LispError LispVal) -> LispVal
       Lambda : (params : List String) -> (vararg : Maybe String) ->
                (body : List LispVal) -> (closure : EnvCtx) -> LispVal

  data LispError : Type where
       NumArgs : (expected : Integer) -> (found : List LispVal) -> LispError
       TypeMisMatch : (expected : String) -> (found : LispVal) -> LispError
       Parser : (err : String) -> LispError
       BadSpecialForm : (msg : String) -> (form : LispVal) -> LispError
       NotFunction : (fname : String) -> LispError
       UnboundVar : (varname : String) -> LispError
       Default : String -> LispError

  EnvCtx : Type
  EnvCtx = IORef (List (String, IORef LispVal))

private
unwordsList : Show a => List a -> String
unwordsList = unwords . map show

export
Show LispVal where
  show (LispAtom atom) = atom
  show (LispNum n) = show n
  show (LispStr str) = "\"" ++ str ++ "\""
  show (LispBool True) = "#t"
  show (LispBool False) = "#f"
  show LispNil = "Nil"
  show (LispList contents) = "(" ++ unwordsList contents ++ ")"
  show (LispDotted contents val)
      = "(" ++ unwordsList contents ++ " . " ++ show val ++ ")"
  show (Function _) = "<primitive>"
  show (Lambda params vararg body closure)
      = "(lambda (" ++ unwordsList params ++
        (case vararg of
              Nothing => ""
              Just arg => " . " ++ arg) ++ ") ...)"

export
Show LispError where
  show (NumArgs expected found) = "Expected " ++ show expected ++
                                " args; found values " ++ unwordsList found
  show (TypeMisMatch expected found) = "Invalid type: expected " ++
                                       expected ++ ", found " ++ show found
  show (Parser err) = "Parser error at " ++ err
  show (BadSpecialForm msg form) = msg ++ ": " ++ show form
  show (NotFunction fname) = fname ++ " is not a function"
  show (UnboundVar varname) = varname ++ " is not bounded"
  show (Default msg) = msg


module Duanwu.LispVal

import public Data.IORef
import public Duanwu.Helper

%access public export

mutual
  data LispVal : Type where
       Atom : String -> LispVal
       Num : Integer -> LispVal
       Str : String -> LispVal
       Bool : Bool -> LispVal
       Nil : LispVal
       List : List LispVal -> LispVal
       Dotted : List LispVal -> LispVal -> LispVal
       Function : (fn : List LispVal -> Either LispError LispVal) -> LispVal
       Lambda : (params : List String) -> (vararg : Maybe String) ->
                (body : List LispVal) -> (closure : EnvCtx) -> LispVal
       IOFunc : (fn : List LispVal -> EitherT LispError IO LispVal) ->
                LispVal
       Port : File -> LispVal

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
  show (Atom atom) = atom
  show (Num n) = show n
  show (Str str) = "\"" ++ str ++ "\""
  show (Bool True) = "#t"
  show (Bool False) = "#f"
  show Nil = "Nil"
  show (List contents) = "(" ++ unwordsList contents ++ ")"
  show (Dotted contents val)
      = "(" ++ unwordsList contents ++ " . " ++ show val ++ ")"
  show (Function _) = "<primitive>"
  show (Lambda params vararg body closure)
      = "(lambda (" ++ unwordsList params ++
        (case vararg of
              Nothing => ""
              Just arg => " . " ++ arg) ++ ") ...)"
  show (IOFunc _) = "<IO primitive>"
  show (Port _) = "<IO port>"

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


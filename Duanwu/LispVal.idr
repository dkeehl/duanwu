module Duanwu.LispVal

import Effects
import Effect.Env

%access public export

data PrimFun = Car
             | Cdr 
             | Cons 
             | Eqv
             | Add 
             | Sub 
             | Mult 
             | Div 
             | Mod
             | And
             | Or
             | EQ
             | LT 
             | GT 
             | NE 
             | LTE 
             | GTE 
             | StrEq 
             | StrLT 
             | StrGT 
             | StrLTE 
             | StrGTE 
             | OpenInputFile 
             | OpenOutputFile 
             | CloseInputFile 
             | CloseOutputFile 
             | Read 
             | Write 
             | ReadContents
             | ReadAll 
             | Apply

data LispVal : Type where
     Atom : String -> LispVal
     Num : Integer -> LispVal
     Str : String -> LispVal
     Bool : Bool -> LispVal
     Nil : LispVal
     List : List LispVal -> LispVal
     Dotted : List LispVal -> LispVal -> LispVal
     Lambda : (params : List String) -> (vararg : Maybe String) ->
              (body : List LispVal) -> (closure : EnvRef LispVal) -> LispVal
     Fun : PrimFun -> LispVal
     -- IOFunc : (fn : List LispVal -> EitherT LispError IO LispVal) ->
     --         LispVal
     Port : File -> LispVal

data LispError : Type where
     NumArgs : (expected : Integer) -> (found : List LispVal) -> LispError
     TypeMisMatch : (expected : String) -> (found : LispVal) -> LispError
     Parser : (err : String) -> LispError
     BadSpecialForm : (msg : String) -> (form : LispVal) -> LispError
     NotFunction : (fname : String) -> LispError
     UnboundVar : (varname : String) -> LispError
     Default : String -> LispError

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
  show (Lambda params vararg body closure)
      = "(lambda (" ++ unwordsList params ++
        (case vararg of
              Nothing => ""
              Just arg => " . " ++ arg) ++ ") ...)"
  show (Fun _) = "<primitive>"
  -- show (IOFunc _) = "<IO primitive>"
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

ok : a -> EffM m (Either LispError a) xs (\v => xs)
ok = pure . Right

err : LispError -> EffM m (Either LispError a) xs (\v => xs) 
err = pure . Left


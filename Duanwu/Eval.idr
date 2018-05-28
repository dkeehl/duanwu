module Duanwu.Eval

import Duanwu.LispVal
import Duanwu.Prim
import Effects
import Effect.Exception
import Effect.Env
import Effect.FileIO

public export
Eval : Type -> Type
Eval a = Eff (Either LispError a) [ENV LispVal, EXCEPTION Panic, FILE_IO]

-- Make functons
mkFunc : (varargs : Maybe String) -> (env : EnvRef LispVal) ->
         (params : List LispVal) -> (body : List LispVal) -> LispVal 
mkFunc varargs env params body
  = Lambda (map show params) varargs body env
    -- need to check all params are atoms?
       
mkNormFunc : (env : EnvRef LispVal) -> (params : List LispVal) ->
             (body : List LispVal) -> LispVal
mkNormFunc = mkFunc Nothing

mkVarArgs : (arg : String) -> (env : EnvRef LispVal) -> (params : List LispVal) ->
            (body : List LispVal) -> LispVal
mkVarArgs = mkFunc . Just 

traverseE: (LispVal -> Eval LispVal) -> List LispVal -> Eval (List LispVal)
traverseE f [] = ok []
traverseE f (x::xs) = do v <- f x
                         vs <- traverseE f xs
                         pure [| v :: vs |]

mutual
  export
  eval : EnvRef LispVal -> LispVal -> Eval LispVal
  eval env val@(Str _) = ok val
  eval env val@(Num _) = ok val
  eval env val@(Bool _) = ok val
  eval env Nil = ok Nil
  eval env (List [Atom "quote", val]) = ok val
  eval env (Atom id) = do Just val <- getVar env id | err (UnboundVar id)
                          ok val
  eval env (List (Atom "lambda" :: List params :: body))
    = ok $ mkNormFunc env params body
  eval env (List (Atom "lambda"
                      :: Dotted params (Atom vararg)
                      :: body))
    = ok $ mkVarArgs vararg env params body
  eval env (List (Atom "lambda" :: Atom vararg :: body))
    = ok $ mkVarArgs vararg env [] body
    
  eval env (List [Atom "set!", Atom var, form])
    = do Right val <- eval env form | Left e => err e
         True <- setVar env var val | err (UnboundVar var)
         ok val
  eval env (List [Atom "define", Atom var, form])
    = do Right val <- eval env form | Left e => err e
         defineVar env var val
         ok val
  eval env
    (List (Atom "define"
              ::  List (Atom var :: params)
              ::  body))
    = do let fn = mkNormFunc env params body
         defineVar env var fn
         ok fn
  eval env
    (List (Atom "define"
              :: Dotted (Atom var :: params) (Atom vararg)
              :: body))
    = do let fn = mkVarArgs vararg env params body
         defineVar env var fn
         ok fn

  eval env (List [Atom "if", pred, conseq, alt])
    = do Right (Bool False) <- eval env pred
          | Left e => err e
          | _ => eval env conseq
         eval env alt

  eval env (List (func :: args))
    = do Right fn <- eval env func | Left e => err e
         Right args' <- traverseE (eval env) args | Left e => err e
         apply fn args' 

  eval env (List [Atom "load", Str filename])
    = do Right xs <- load filename | Left e => err e
         Right (x :: ys) <- traverseE (eval env) xs
          | Right [] => ok Nil
          | Left e => err e
         ok $ last (x :: ys)

  eval env val = err $ Default ("unmatched case " ++ show val)

  apply : LispVal -> List LispVal -> Eval LispVal
  apply (Fun Apply) [fn, List args] = apply fn args
  apply (Fun Apply) (fn::args) = apply fn args
  apply (Fun Apply) _ = err $ Default "apply: expected 2 or more arguments"
  apply (Fun fn) args = runPrim fn args
  apply (Lambda params vararg body closure) args
    = if length params /= length args && vararg == Nothing
         then err $ NumArgs (cast $ length params) args
         else do Right (x :: xs) <- evalBody !localEnv body
                  | Right [] => err (Default "empty body")
                  | Left e => err e
                 ok $ last (x :: xs)
    where optArg : List (String, LispVal)
          optArg 
            = let remaining = drop (length params) args in 
                  case vararg of
                       Nothing  => []
                       Just arg => [(arg, List remaining)]
          localEnv : Eff (EnvRef LispVal) [ENV LispVal]
          localEnv = local closure $ zip params args ++ optArg
          evalBody : EnvRef LispVal -> List LispVal -> Eval (List LispVal)
          evalBody env = traverseE (eval env)

  apply expr _ = err $ NotFunction (show expr)

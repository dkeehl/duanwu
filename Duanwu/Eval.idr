module Duanwu.Eval

import Duanwu.LispVal
import Duanwu.Parser

export
load : String -> EitherT LispError IO (List LispVal)
load filename = do Right str <- lift $ readFile filename
                    | Left err => left (Default $ show err)
                   liftEither $ readExprList str

-- Environment related
public export
Eval : Type -> Type
Eval = EitherT LispError IO

isBound : EnvCtx -> String -> IO Bool
isBound envRef var = do env <- readIORef envRef
                        case lookup var env of
                             Just _ => pure True
                             Nothing => pure False

getVar : (envRef : EnvCtx) -> (k : String) -> Eval LispVal
getVar envRef k = do env <- lift $ readIORef envRef
                     case lookup k env of
                          Nothing => left $ UnboundVar k
                          Just ref => lift $ (readIORef ref) 

setVar : EnvCtx -> (var : String) -> (val : LispVal) -> Eval LispVal
setVar envRef var val = do env <- lift $ readIORef envRef
                           case lookup var env of
                                Nothing => left $ UnboundVar var
                                Just ref => lift $ (writeIORef ref val)
                           pure val

defineVar : EnvCtx -> (var : String) -> (val : LispVal) -> Eval LispVal
defineVar envRef var val
  = do if !(lift $ isBound envRef var)
          then setVar envRef var val
          else lift $ do valRef <- newIORef val
                         modifyIORef envRef ((var, valRef) ::)
                         pure val

export
bindVars : (old : EnvCtx) -> (varList : List (String, LispVal)) ->
           IO EnvCtx 
bindVars envRef varList = do env <- readIORef envRef
                             let bindings = traverse addBinding varList
                             newIORef !(liftA (++ env) bindings)
  where addBinding : (String, LispVal) -> IO (String, IORef LispVal)
        addBinding (k, v) = do ref <- newIORef v
                               pure (k, ref)


-- Make functons
mkFunc : (varargs : Maybe String) -> (env : EnvCtx) ->
         (params : List LispVal) -> (body : List LispVal) ->
         Eval LispVal 
mkFunc varargs env params body
  = pure $ Lambda (map show params) varargs body env
    -- need to check all params are atoms?
       
mkNormFunc : (env : EnvCtx) -> (params : List LispVal) ->
             (body : List LispVal) -> Eval LispVal
mkNormFunc = mkFunc Nothing

mkVarArgs : (arg : String) -> (env : EnvCtx) -> (params : List LispVal) ->
            (body : List LispVal) -> Eval LispVal
mkVarArgs = mkFunc . Just 


-- Evaluation function
mutual
  export
  eval : (env : EnvCtx) -> LispVal -> Eval LispVal
  eval env val@(Str _) = pure val
  eval env val@(Num _) = pure val
  eval env val@(Bool _) = pure val
  eval env Nil = pure Nil
  eval env (List [Atom "quote", val]) = pure val
  eval env (Atom id) = getVar env id
  eval env (List [Atom "if", pred, conseq, alt])
    = do Bool False <- eval env pred
          | _ => eval env conseq
         eval env alt
  eval env (List [Atom "define", Atom var, form])
    = eval env form >>= defineVar env var
  eval env (List [Atom "set!", Atom var, form])
    = eval env form >>= setVar env var
  eval env (List [Atom "load", Str filename])
    = do xs <- load filename
         (x :: ys) <- traverse (eval env) xs
          | [] => pure Nil
         pure $ last (x :: ys)
  eval env
    (List (Atom "define"
              ::  List (Atom var :: params)
              ::  body))
    = mkNormFunc env params body >>= defineVar env var
  eval env
    (List (Atom "define"
              :: Dotted (Atom var :: params) (Atom vararg)
              :: body))
    = mkVarArgs vararg env params body >>= defineVar env var
  eval env (List (Atom "lambda" :: List params :: body))
    = mkNormFunc env params body
  eval env (List (Atom "lambda"
                      :: Dotted params (Atom vararg)
                      :: body))
    = mkVarArgs vararg env params body
  eval env (List (Atom "lambda" :: Atom vararg :: body))
    = mkVarArgs vararg env [] body
  eval env (List (func :: args))
    = do fn <- eval env func
         args' <- traverse (eval env) args
         apply fn args' 

  eval env val = left $ Default ("unmatched case " ++ show val)

  export                 
  apply : LispVal -> List LispVal -> Eval LispVal
  apply (Function fn) args = liftEither (fn args)
  apply (IOFunc fn) args = fn args
  apply (Lambda params vararg body closure) args
    = if length params /= length args && vararg == Nothing
         then left $ NumArgs (cast $ length params) args
         else do (x :: xs) <- evalBody !(lift local) body
                  | [] => left (Default "empty body")
                 pure $ last (x :: xs)
    where optArg : List (String, LispVal)
          optArg 
            = let remaining = drop (length params) args in 
                  case vararg of
                       Nothing  => []
                       Just arg => [(arg, List remaining)]
          local : IO EnvCtx
          local = bindVars closure $ zip params args ++ optArg
          evalBody : EnvCtx -> List LispVal -> Eval (List LispVal)
          evalBody env = traverse (eval env)

  apply expr _ = left $ NotFunction (show expr)


module Duanwu.Eval

import Duanwu.LispVal
import Duanwu.Helper
import Duanwu.Parser
import Data.IORef
import Control.Monad.Trans

export
mapM : Monad m => (a -> m b) -> List a -> m (List b)
mapM _ [] = pure []
mapM f (x :: xs) = do x' <- f x
                      xs' <- mapM f xs
                      pure $ x' :: xs'

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
                             let bindings = mapM addBinding varList
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
  eval env val@(LispStr _) = pure val
  eval env val@(LispNum _) = pure val
  eval env val@(LispBool _) = pure val
  eval env LispNil = pure LispNil
  eval env (LispList [LispAtom "quote", val]) = pure val
  eval env (LispAtom id) = getVar env id
  eval env (LispList [LispAtom "if", pred, conseq, alt])
    = do LispBool False <- eval env pred
          | _ => eval env conseq
         eval env alt
  eval env (LispList [LispAtom "define", LispAtom var, form])
    = eval env form >>= defineVar env var
  eval env (LispList [LispAtom "set!", LispAtom var, form])
    = eval env form >>= setVar env var
  eval env (LispList [LispAtom "load", LispStr filename])
    = do xs <- load filename
         (x :: ys) <- mapM (eval env) xs
          | [] => pure LispNil
         pure $ last (x :: ys)
  eval env
    (LispList (LispAtom "define"
              ::  LispList (LispAtom var :: params)
              ::  body))
    = mkNormFunc env params body >>= defineVar env var
  eval env
    (LispList (LispAtom "define"
              :: LispDotted (LispAtom var :: params) (LispAtom vararg)
              :: body))
    = mkVarArgs vararg env params body >>= defineVar env var
  eval env (LispList (LispAtom "lambda" :: LispList params :: body))
    = mkNormFunc env params body
  eval env (LispList (LispAtom "lambda"
                      :: LispDotted params (LispAtom vararg)
                      :: body))
    = mkVarArgs vararg env params body
  eval env (LispList (LispAtom "lambda" :: LispAtom vararg :: body))
    = mkVarArgs vararg env [] body
  eval env (LispList (func :: args))
    = do fn <- eval env func
         args' <- mapM (eval env) args
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
                       Just arg => [(arg, LispList remaining)]
          local : IO EnvCtx
          local = bindVars closure $ zip params args ++ optArg
          evalBody : EnvCtx -> List LispVal -> Eval (List LispVal)
          evalBody env = mapM (eval env)

  apply expr _ = left $ NotFunction (show expr)


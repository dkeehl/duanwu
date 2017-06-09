module Duanwu.Eval

import Duanwu.LispVal
import Duanwu.Helper
import Data.IORef
import Control.Monad.Trans

mapM : Monad m => (a -> m b) -> List a -> m (List b)
mapM _ [] = pure []
mapM f (x :: xs) = do x' <- f x
                      xs' <- mapM f xs
                      pure $ x' :: xs'

-- Buildin functions
interface Convert ty where
  conv : LispVal -> Either LispError ty

Convert Integer where
  conv (LispNum n) = Right n
  conv (LispStr str)
      = if all isDigit (unpack str)
           then Right $ cast str
           else Left $ TypeMisMatch "number" (LispStr str)
  conv (LispList [n]) = conv n
  conv notNum = Left $ TypeMisMatch "number" notNum 

Convert String where
  conv (LispNum x) = Right (show x)
  conv (LispStr x) = Right x
  conv val@(LispBool _) = Right (show val)
  conv notString = Left $ TypeMisMatch "string" notString

Convert Bool where
  conv (LispBool b) = Right b
  conv notBool = Left $ TypeMisMatch "boolean" notBool

numericBinop : (Integer -> Integer -> Integer) ->
               List LispVal -> Either LispError LispVal
numericBinop op [] = Left $ NumArgs 2 []
numericBinop op params = do nums <- mapM conv params
                            pure $ LispNum (foldl1 op nums)

boolBinop : Convert a => (a -> a -> Bool) -> List LispVal ->
                         Either LispError LispVal
boolBinop op [x, y] = do x' <- conv x
                         y' <- conv y
                         pure $ LispBool (op x' y')
boolBinop _ args = Left $ NumArgs 2 args

car : List LispVal -> Either LispError LispVal
car [LispList (x :: xs)] = Right x
car [LispDotted (x :: xs) _] = Right x
car [badArg] = Left $ TypeMisMatch "pair" badArg
car badArgList = Left $ NumArgs 1 badArgList

cdr : List LispVal -> Either LispError LispVal
cdr [LispList [_]] = Right $ LispNil
cdr [LispList (_ :: xs)] = Right $ LispList xs
cdr [LispDotted [_] x] = Right x
cdr [LispDotted (_ :: xs) x] = Right $ LispDotted xs x
cdr [badArg] = Left $ TypeMisMatch "pair" badArg
cdr badArgList = Left $ NumArgs 1 badArgList

cons : List LispVal -> Either LispError LispVal
cons [x, LispNil] = Right $ LispList [x]
cons [x, LispList xs] = Right $ LispList (x :: xs)
cons [x, LispDotted xs xlast] = Right $ LispDotted (x :: xs) xlast
cons [x, y] = Right $ LispDotted [x] y
cons badArgList = Left $ NumArgs 2 badArgList

eqv : List LispVal -> Either LispError LispVal
eqv [LispBool b1, LispBool b2] = Right $ LispBool (b1 == b2)
eqv [LispNum n1, LispNum n2] = Right $ LispBool (n1 == n2)
eqv [LispStr s1, LispStr s2] = Right $ LispBool (s1 == s2)
eqv [LispAtom a1, LispAtom a2] = Right $ LispBool (a1 == a2)
eqv [LispNil, LispNil] = Right $ LispBool True
eqv [LispList [], LispList []] = Right $ LispBool True
eqv [LispList [], LispList _] = Right $ LispBool False
eqv [LispList _, LispList []] = Right $ LispBool False
eqv [LispList (x :: xs), LispList (y :: ys)]
    = do LispBool True <- eqv [x, y] | _ => pure (LispBool False)
         eqv [LispList xs, LispList ys]
eqv [LispDotted xs x, LispDotted ys y]
    = eqv [LispList (xs ++ [x]), LispList (ys ++ [y])]
eqv [_, _] = Right $ LispBool False
eqv badArgList = Left $ NumArgs 2 badArgList

primitives : List (String,  List LispVal -> Either LispError LispVal)
primitives = [("+", numericBinop (+)),
              ("-", numericBinop (-)),
              ("*", numericBinop (*)),
              ("/", numericBinop div),
              ("quotient", numericBinop div),
              ("remainder", numericBinop mod),
              ("car", car),
              ("cdr", cdr),
              ("cons", cons),
              ("eq?", eqv),
              ("eqv?", eqv),
              ("=", boolBinop $ (==) {ty = Integer}),
              ("<", boolBinop $ (<) {ty = Integer}),
              (">", boolBinop $ (>) {ty = Integer}),
              ("/=", boolBinop $ (/=) {ty = Integer}),
              (">=", boolBinop $ (>=) {ty = Integer}),
              ("<=", boolBinop $ (<=) {ty = Integer}),
              ("&&", boolBinop (\x, y => x && y)),
              ("||", boolBinop (\x, y => x || y)),
              ("string=?", boolBinop $ (==) {ty = String}),
              ("string<?", boolBinop $ (<) {ty = String}),
              ("string>?", boolBinop $ (>) {ty = String}),
              ("string<=?", boolBinop $ (<=) {ty = String}),
              ("string>=?", boolBinop $ (>=) {ty = String})]

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

bindVars : (old : EnvCtx) -> (varList : List (String, LispVal)) ->
           IO EnvCtx 
bindVars envRef varList = do env <- readIORef envRef
                             let bindings = mapM addBinding varList
                             newIORef !(liftA (++ env) bindings)
  where addBinding : (String, LispVal) -> IO (String, IORef LispVal)
        addBinding (k, v) = do ref <- newIORef v
                               pure (k, ref)

nullEnv : IO EnvCtx
nullEnv = newIORef []

export
primitiveBindings : IO EnvCtx
primitiveBindings
  = let mkPrimFunctions = \(var, func) => (var, Function func) in
        nullEnv >>= flip bindVars (map mkPrimFunctions primitives)

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

                 
  apply : LispVal -> List LispVal -> Eval LispVal
  apply (Function fn) args = liftEither (fn args)
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


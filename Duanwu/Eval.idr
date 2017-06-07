module Duanwu.Eval

import Duanwu.LispVal
import Data.SortedMap
import Control.ST

mapM : Monad m => (a -> m b) -> List a -> m (List b)
mapM _ [] = pure []
mapM f (x :: xs) = do x' <- f x
                      xs' <- mapM f xs
                      pure $ x' :: xs'

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

export
pureL : e -> STrans m (Either e a) res (const res)
pureL = pure . Left

export
pureR : a -> STrans m (Either e a) res (const res)
pureR = pure . Right

mapST : (a -> STrans m (Either e b) st (const st)) -> List a ->
        STrans m (Either e (List b)) st (const st)
mapST f [] = pureR []
mapST f (x :: xs) = do Right x' <- f x
                        | Left err => pureL err
                       Right xs' <- mapST f xs
                        | Left err => pureL err
                       pureR (x' :: xs')

{-
export
liftEither : Exception m e => Either e a -> STrans m a res (const res)
liftEither (Left err) = throw err
liftEither (Right val) = pure val
-}

updateVar : (env : Var) -> (k : String) -> (v : LispVal) ->
            ST m () [env ::: State EnvCtx]
updateVar env k v = update env (insert k v)

bindVars : (old : EnvCtx) -> (varList : List (String, LispVal)) -> EnvCtx
bindVars = foldl (\env, (k, v) => insert k v env)

public export
Eval : (m : Type -> Type) -> (a : Type) ->
       List (Action $ Either LispError a) -> Type
Eval m a = ST m (Either LispError a)

mkFunc : (varargs : Maybe String) -> (env : Var) ->
         (params : List LispVal) -> (body : List LispVal) ->
         Eval m LispVal [env ::: State EnvCtx]
mkFunc varargs env params body
  = do closure <- read env
       -- need to check all params are atoms?
       pureR $ Lambda (map show params) varargs body closure

mkNormFunc : (env : Var) -> (params : List LispVal) ->
             (body : List LispVal) -> Eval m LispVal [env ::: State EnvCtx]
mkNormFunc = mkFunc Nothing

mkVarArgs : (arg : String) -> (env : Var) -> (params : List LispVal) ->
            (body : List LispVal) -> Eval m LispVal [env ::: State EnvCtx]
mkVarArgs = mkFunc . Just 

mutual
  export
  eval : (env : Var) -> LispVal -> Eval m LispVal [env ::: State EnvCtx]
  eval env val@(LispStr _) = pureR val
  eval env val@(LispNum _) = pureR val
  eval env val@(LispBool _) = pureR val
  eval env LispNil = pureR LispNil
  eval env (LispList [LispAtom "quote", val]) = pureR val
  eval env (LispAtom id)
    = case lookup id !(read env) of
           Nothing => pureL $ UnboundVar "Unbound variable" id
           Just val => pureR val
  eval env (LispList [LispAtom "if", pred, conseq, alt])
    = do Right (LispBool False) <- eval env pred
          | Right _ => eval env conseq
          | Left err => pureL err
         eval env alt
  eval env (LispList [LispAtom "define", LispAtom var, form])
    = do Right val <- eval env form
          | Left err => pureL err
         updateVar env var val
         pureR val
  eval env (LispList [LispAtom "set!", LispAtom var, form])
    = do e <- read env 
         case lookup var e of
              Nothing => pure $
                        Left (UnboundVar "Setting an unbound variable" var)
              Just _ => do Right val <- eval env form
                            | Left err => pureL err
                           updateVar env var val
                           pureR val
  eval env
    (LispList (LispAtom "define"
              ::  LispList (LispAtom var :: params)
              ::  body))
    = do Right fn <- mkNormFunc env params body
          | Left err => pureL err
         updateVar env var fn
         pureR $ LispAtom var
  eval env
    (LispList (LispAtom "define"
              :: LispDotted (LispAtom var :: params) (LispAtom vararg)
              :: body))
    = do Right fn <- mkVarArgs vararg env params body
          | Left err => pureL err
         updateVar env var fn
         pureR $ LispAtom var
  eval env (LispList (LispAtom "lambda" :: LispList params :: body))
    = mkNormFunc env params body
  eval env (LispList (LispAtom "lambda"
                      :: LispDotted params (LispAtom vararg)
                      :: body))
    = mkVarArgs vararg env params body
  eval env (LispList (LispAtom "lambda" :: LispAtom vararg :: body))
    = mkVarArgs vararg env [] body
  eval env (LispList (func :: args))
    = do Right fn <- eval env func
          | Left err => pureL err
         Right args' <- mapST (eval env) args
          | Left err => pureL err
         apply env fn args' 

  eval env val = pureL $ Default ("unmatched case " ++ show val)

  localEval : (local : EnvCtx) -> List LispVal ->
              Eval m (List LispVal) []
  localEval local es = do env <- new local
                          val <- mapST (eval env) es
                          delete env
                          pure val
                 
  apply : (env : Var) -> LispVal -> List LispVal ->
          Eval m LispVal [env ::: State EnvCtx]
  apply env (Function fn) args = pure (fn args)
  apply env (Lambda params vararg body closure) args
    = if length params /= length args && vararg == Nothing
         then pureL $ NumArgs (cast $ length params) args
         else do Right (x :: xs) <- call $ localEval local body
                  | Right [] => pureL (Default "empty body")
                  | Left err => pureL err
                 pureR $ last (x :: xs)
    where optArg : List (String, LispVal)
          optArg 
            = let remaining = drop (length params) args in 
                  case vararg of
                       Nothing  => []
                       Just arg => [(arg, LispList remaining)]
          local : EnvCtx
          local = bindVars closure $ zip params args ++ optArg

  apply env expr _ = eval env expr

export
primitiveBindings : EnvCtx
primitiveBindings
  = let mkPrimFunctions = \(var, func) => (var, Function func) in
        bindVars empty $ map mkPrimFunctions primitives

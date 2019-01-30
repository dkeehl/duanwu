module Duanwu.Syntax

import Data.IORef

%default total

mutual
  data Definition : Type where
    DefVar : String -> Expression -> Definition
    DefFun : String -> List String -> Body -> Definition

  data Body : Type where
    MkBody : List Definition -> Expression -> List Expression -> Body

  data Expression : Type where
    ConstI : Integer -> Expression
    ConstB : Bool -> Expression
    Var : String -> Expression
    Quote : Expression -> Expression
    Lambda : List String -> Body -> Expression
    If : Expression -> Expression -> Expression -> Expression
    MutSet : String -> Expression -> Expression
    Apply : Expression -> List Expression -> Expression
    CallCC : String -> Body -> Expression

data Form = Def Definition | Expr Expression

data Error = NotDefined | WrongArgNumber

record Eval a where
  constructor MkEval
  runEval : IO (Either Error a)

-- Functor
map : (a -> b) -> Eval a -> Eval b
map f (MkEval ioe) = MkEval $ map (map f) ioe

-- Applicative
%inline
pure : a -> Eval a
pure x = MkEval (pure (pure x))

(<*>) : Eval (a -> b) -> Eval a -> Eval b
(<*>) (MkEval mmf) (MkEval mma) = MkEval [| mmf <*> mma |]

-- Monad
%inline
(>>=) : Eval a -> (a -> Eval b) -> Eval b
(>>=) (MkEval ioe) f
  = MkEval (ioe >>= \e => case e of
           Left err  => pure (Left err)
           Right val => runEval (f val))

%inline
liftIO : IO a -> Eval a
liftIO io = MkEval (map Right io)

fail : Error -> Eval a
fail = MkEval . pure . Left

data Env : Type -> Type where
  MkEnv : IORef (List (String, IORef a)) -> Env a

get : Env a -> String -> Eval (Maybe a)

put : Env a -> String -> a -> Eval a

local : Env a -> List (String, a) -> Eval (Env a)

mutual
  data Continuation : Type where
    Return : Continuation
    Branch : Expression -> Expression -> Env Value -> Continuation -> Continuation
    EvalArgs : List Expression -> Env Value -> Continuation -> Continuation
    Seq : List Expression -> Env Value -> Continuation -> Continuation

  data Value : Type where
    Void : Value
    E : Expression -> Value
    I : Integer -> Value
    B : Bool -> Value
    Closure : Expression -> Env Value -> Value
    Cont : Continuation -> Value

mkFunc : Env Value -> List String -> Body -> Value
mkFunc env args body = Closure (Lambda args body) env

%default covering
mutual
  evalDef : Definition -> Env Value -> Eval Value
  evalDef (DefVar name expr) env = do val <- evalExpr expr env Return
                                      put env name val
  evalDef (DefFun name args body) env = do let fn = mkFunc env args body
                                           put env name fn
                                           pure fn

  evalExpr : Expression -> Env Value -> Continuation -> Eval Value
  evalExpr (ConstI i) env c = runCont c (I i)
  evalExpr (ConstB b) env c = runCont c (B b)
  evalExpr (Var name) env c = do Just val <- get env name
                                 | Nothing => fail NotDefined
                                 runCont c val
  evalExpr (Quote e) env c = runCont c (E e)
  evalExpr (Lambda args body) env c = runCont c $ mkFunc env args body
  evalExpr (If pred conseq alt) env c = let cont = Branch conseq alt env c in
                                            evalExpr pred env cont
  evalExpr (MutSet name e) env c = do val <- evalExpr e env Return
                                      put env name val
                                      runCont c Void
  evalExpr (Apply f args) env c = let cont = EvalArgs args env c in
                                      evalExpr f env cont
  evalExpr (CallCC name (MkBody defs expr es)) env c
    = do let cc = Cont c
         localEnv <- local env [(name, cc)]
         evalBody defs expr es localEnv c

  evalBody : List Definition -> Expression -> List Expression ->
             Env Value -> Continuation -> Eval Value
  evalBody [] expr es env c = let cont = Seq es env c in
                                  evalExpr expr env cont
  evalBody (def::defs) expr es env c = do evalDef def env
                                          evalBody defs expr es env c

  runCont : Continuation -> Value -> Eval Value
  runCont Return x = pure x
  runCont (Branch conseq alt env next) x
    = case x of
           B False => evalExpr alt env next
           _       => evalExpr conseq env next
  runCont (EvalArgs es env c) f = evalArgs es env (\xs => apply f xs c)
    where
      evalArgs : List Expression -> Env Value ->
                 (k: List Value -> Eval Value) -> Eval Value
      evalArgs []      env k = k []
      evalArgs (e::es) env k = do x <- evalExpr e env Return
                                  let k' = \xs => k (x::xs)
                                  evalArgs es env k'
  runCont (Seq es env c) x
    = case es of
           []     => runCont c x
           e::es' => evalExpr e env $ Seq es' env c

  apply : Value -> List Value -> Continuation -> Eval Value
  apply (Closure (Lambda names (MkBody defs expr es)) env) args next
    = do localEnv <- local env (zip names args)
         evalBody defs expr es localEnv next
  apply (Closure _ _) _ _ = assert_unreachable
  apply (Cont c) [x] _ = runCont c x
  apply (Cont _) _ _ = fail WrongArgNumber
  apply f args c = ?hole3

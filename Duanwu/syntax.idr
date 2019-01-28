module Duanwu.Syntax

-- import Duanwu.Lexer

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

data Env : Type -> Type where
  MkEnv : Env a

data Eval : Type -> Type where
  Pure : a -> Eval a
  Bind : Eval a -> (a -> Eval b) -> Eval b
  Get : Env a -> String -> Eval a
  Set : Env a -> String -> a -> Eval a
  Local : Env a -> List (String, a) -> Eval (Env a)
  Defined : String -> Eval Bool

pure : a -> Eval a
pure = Pure

(>>=) : Eval a -> (a -> Eval b) -> Eval b
(>>=) = Bind

get : Env a -> String -> Eval a
get = Get

set : Env a -> String -> a -> Eval a
set = Set

local : Env a -> List (String, a) -> Eval (Env a)
local = Local

isDefined : String -> Eval Bool
isDefined = Defined

mutual
  data Continuation : Type where
    Return : Continuation
    Branch : Expression -> Expression -> Env Value -> Continuation -> Continuation
    EvalArgs : (todo: List Expression) ->
               (done: List Value) ->
               Env Value -> Continuation -> Continuation
    Seq : List Expression -> Env Value -> Continuation -> Continuation

  data Value : Type where
    E : Expression -> Value
    I : Integer -> Value
    B : Bool -> Value
    Closure : Expression -> Env Value -> Value
    Cont : Continuation -> Value

runEval : Eval a -> IO a

mkFunc : Env Value -> List String -> Body -> Value
mkFunc env args body = Closure (Lambda args body) env

%default covering
mutual
  evalDef : Definition -> Env Value -> Eval Value
  evalDef (DefVar name expr) env = do val <- evalExpr expr env Return
                                      set env name val
  evalDef (DefFun name args body) env = do let fn = mkFunc env args body
                                           set env name fn
                                           pure fn

  evalExpr : Expression -> Env Value -> Continuation -> Eval Value
  evalExpr (ConstI i) env c = runCont c (I i)
  evalExpr (ConstB b) env c = runCont c (B b)
  evalExpr (Var name) env c = do val <- get env name
                                 runCont c val
  evalExpr (Quote e) env c = runCont c (E e)
  evalExpr (Lambda args body) env c = runCont c $ mkFunc env args body
  evalExpr (If pred conseq alt) env c = let cont = Branch conseq alt env c in
                                            evalExpr pred env cont
  evalExpr (MutSet name e) env c = ?hole0
  evalExpr (Apply f args) env c = let cont = EvalArgs args [] env c in
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
  runCont (EvalArgs es xs env c) x
    = case es of
           []    => apply x (reverse xs) c
           a::as => let cont = EvalArgs as (x::xs) env c in
                        evalExpr a env c
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
  apply (Cont _) _ _ = ?hole1
  apply f args c = ?hole3


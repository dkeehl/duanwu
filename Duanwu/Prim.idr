module Duanwu.Prim

import Duanwu.LispVal
import Duanwu.Parser
import Effects
import Effect.Exception
import Effect.FileIO

Result : Type -> Type
Result = Either LispError

-- Buildin functions
interface Convert ty where
  conv : LispVal -> Result ty

Convert Integer where
  conv (Num n) = pure n
  conv (Str str)
      = if all isDigit (unpack str)
           then pure $ cast str
           else Left $ TypeMisMatch "number" (Str str)
  conv (List [n]) = conv n
  conv notNum = Left $ TypeMisMatch "number" notNum 

Convert String where
  conv (Num x) = pure (show x)
  conv (Str x) = pure x
  conv val@(Bool _) = pure (show val)
  conv notString = Left $ TypeMisMatch "string" notString

Convert Bool where
  conv (Bool b) = pure b
  conv notBool = Left $ TypeMisMatch "boolean" notBool

numericBinop : (Integer -> Integer -> Integer) ->
               List LispVal -> Result LispVal
numericBinop op [] = Left $ NumArgs 2 []
numericBinop op (v::vs) = do x <- conv v
                             y <- conv !(numericBinop op vs)
                             pure $ Num (op x y)

boolBinop : Convert a => (a -> a -> Bool) -> List LispVal -> Result LispVal
boolBinop op [x, y] = do x' <- conv x
                         y' <- conv y
                         pure $ Bool (op x' y')
boolBinop _ args = Left $ NumArgs 2 args

car : List LispVal -> Result LispVal
car [List (x :: xs)] = pure x
car [Dotted (x :: xs) _] = pure x
car [badArg] = Left $ TypeMisMatch "pair" badArg
car badArgList = Left $ NumArgs 1 badArgList

cdr : List LispVal -> Result LispVal
cdr [List [_]] = pure $ Nil
cdr [List (_ :: xs)] = pure $ List xs
cdr [Dotted [_] x] = pure x
cdr [Dotted (_ :: xs) x] = pure $ Dotted xs x
cdr [badArg] = Left $ TypeMisMatch "pair" badArg
cdr badArgList = Left $ NumArgs 1 badArgList

cons : List LispVal -> Result LispVal
cons [x, Nil] = pure $ List [x]
cons [x, List xs] = pure $ List (x :: xs)
cons [x, Dotted xs xlast] = pure $ Dotted (x :: xs) xlast
cons [x, y] = pure $ Dotted [x] y
cons badArgList = Left $ NumArgs 2 badArgList

eqv : List LispVal -> Result LispVal
eqv [Bool b1, Bool b2] = pure $ Bool (b1 == b2)
eqv [Num n1, Num n2] = pure $ Bool (n1 == n2)
eqv [Str s1, Str s2] = pure $ Bool (s1 == s2)
eqv [Atom a1, Atom a2] = pure $ Bool (a1 == a2)
eqv [Nil, Nil] = pure $ Bool True
eqv [List [], List []] = pure $ Bool True
eqv [List [], List _] = pure $ Bool False
eqv [List _, List []] = pure $ Bool False
eqv [List (x :: xs), List (y :: ys)]
    = do Bool True <- eqv [x, y] | _ => pure (Bool False)
         eqv [List xs, List ys]
eqv [Dotted xs x, Dotted ys y]
    = eqv [List (xs ++ [x]), List (ys ++ [y])]
eqv [_, _] = pure $ Bool False
eqv badArgList = Left $ NumArgs 2 badArgList


-- Primitive IO Functions
IOResult : Type -> Type
IOResult a = Eff (Either LispError a) [FILE_IO] 

makePort : Mode -> List LispVal -> IOResult LispVal
makePort mode [Str filename]
  = do Right file <- openFile filename mode
        | Left e => err (Default $ "can't open file " ++ filename ++
                             " " ++ show e)
       ok (Port file)
makePort _ [val] = err $ TypeMisMatch "string" val
makePort _ expr = err $ NumArgs 1 expr

closePort : List LispVal -> IOResult LispVal
closePort [Port file] = do closeFile file
                           ok $ Bool True 
closePort _ = ok $ Bool False

readProc : List LispVal -> IOResult LispVal 
readProc [] = readProc [Port stdin]
readProc [Port port] = do Right str <- fGetLine port
                            | Left e => err (Default (show e))
                          pure $ readExpr str
readProc [val] = err $ TypeMisMatch "port" val
readProc xs = err $ NumArgs 1 xs

writeProc : List LispVal -> IOResult LispVal
writeProc [obj] = do r <- fPutStr stdout (show obj)
                     ok . Bool $ either (const False) (const True) r
writeProc [obj, Port file] = do r <- fPutStr file (show obj)
                                ok . Bool $ either (const False) (const True) r
writeProc _ = err $ Default "write: Invalid arguments"

readContents : List LispVal -> IOResult LispVal
readContents [Str filename]
  = do Right str <- readFile filename
        | Left e => err (Default $ show e)
       ok $ Str str
readContents [val] = err $ TypeMisMatch "string" val
readContents xs = err $ NumArgs 1 xs

export
load : String -> Eff (Either LispError (List LispVal)) [FILE_IO]
load filename = do Right str <- readFile filename
                    | Left e => err (Default $ show e)
                   pure $ readExprList str

readAll : List LispVal -> IOResult LispVal
readAll [Str filename] = do l <- load filename; pure (map List l)
readAll [val] = err $ TypeMisMatch "string" val
readAll expr = err $ NumArgs 1 expr

primFuns : List (String, PrimFun)
primFuns = [("+", Add),
            ("-", Sub),
            ("*", Mult),
            ("/", Div),
            ("quotient", Div),
            ("remainder", Mod),
            ("car", Car),
            ("cdr", Cdr),
            ("cons", Cons),
            ("eq?", Eqv),
            ("eqv?", Eqv),
            ("=", EQ),
            ("<", LT),
            (">", GT),
            ("/=", NE),
            (">=", GTE),
            ("<=", LTE),
            ("&&", And),
            ("||", Or),
            ("string=?", StrEq),
            ("string<?", StrLT),
            ("string>?", StrGT),
            ("string<=?", StrLTE),
            ("string>=?", StrGTE),
            ("open-input-file", OpenInputFile),
            ("open-output-file", OpenOutputFile),
            ("close-input-file", CloseInputFile),
            ("close-output-file", CloseOutputFile),
            ("read", Read),
            ("write", Write),
            ("read-contents", ReadContents),
            ("read-all", ReadAll)]

export
primitives : List (String, LispVal)
primitives = map (map Fun) primFuns

export
runPrim : PrimFun -> List LispVal ->
          Eff (Either LispError LispVal) [EXCEPTION Panic, FILE_IO]
runPrim Car args = pure $ car args  -- point free don't type check, a bug?
runPrim Cdr args = pure $ cdr args
runPrim Cons args = pure $ cons args
runPrim Eqv args = pure $ eqv args
runPrim Add args = pure $ numericBinop (+) args
runPrim Sub args = pure $ numericBinop (-) args
runPrim Mult args = pure $ numericBinop (*) args
runPrim Div args = pure $ numericBinop div args
runPrim Mod args = pure $ numericBinop mod args
runPrim And args = pure $ boolBinop (\x, y => x && y) args
runPrim Or args = pure $ boolBinop (\x, y => x || y) args
runPrim EQ args = pure $ boolBinop {a = Integer} (==) args
runPrim LT args = pure $ boolBinop {a = Integer} (<) args
runPrim GT args = pure $ boolBinop {a = Integer} (>) args
runPrim NE args = pure $ boolBinop {a = Integer} (/=) args
runPrim LTE args = pure $ boolBinop {a = Integer} (<=) args
runPrim GTE args = pure $ boolBinop {a = Integer} (>=) args
runPrim StrEq args = pure $ boolBinop {a = String} (==) args
runPrim StrLT args = pure $ boolBinop {a = String} (<) args
runPrim StrGT args = pure $ boolBinop {a = String} (>) args
runPrim StrLTE args = pure $ boolBinop {a = String} (<=) args
runPrim StrGTE args = pure $ boolBinop {a = String} (>=) args
runPrim OpenInputFile args = makePort Read args 
runPrim OpenOutputFile args = makePort WriteTruncate args
runPrim CloseInputFile args = closePort args
runPrim CloseOutputFile args = closePort args
runPrim Read args = readProc args
runPrim Write args = writeProc args
runPrim ReadContents args = readContents args
runPrim ReadAll args = readAll args
runPrim Apply _ = raise $ Unreachable "Apply: PrimFun should not run in runPrim"

{-
nullEnv : IO EnvCtx
nullEnv = newIORef []

export
primitiveBindings : IO EnvCtx
primitiveBindings
  = let mkPrimFunctions = \(var, func) => (var, Function func)
        mkList LispVal -> IOResult LispVals = \(var, func) => (var, IOFunc func) in
        nullEnv >>= flip bindVars (map mkPrimFunctions primitives
                                  ++ map mkList LispVal -> IOResult LispVals ioPrimitives)
-}

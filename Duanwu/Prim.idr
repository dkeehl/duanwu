module Duanwu.Prim

import Duanwu.LispVal
import Duanwu.Parser
import Duanwu.Eval

-- Buildin functions
interface Convert ty where
  conv : LispVal -> Either LispError ty

Convert Integer where
  conv (Num n) = Right n
  conv (Str str)
      = if all isDigit (unpack str)
           then Right $ cast str
           else Left $ TypeMisMatch "number" (Str str)
  conv (List [n]) = conv n
  conv notNum = Left $ TypeMisMatch "number" notNum 

Convert String where
  conv (Num x) = Right (show x)
  conv (Str x) = Right x
  conv val@(Bool _) = Right (show val)
  conv notString = Left $ TypeMisMatch "string" notString

Convert Bool where
  conv (Bool b) = Right b
  conv notBool = Left $ TypeMisMatch "boolean" notBool

numericBinop : (Integer -> Integer -> Integer) ->
               List LispVal -> Either LispError LispVal
numericBinop op [] = Left $ NumArgs 2 []
numericBinop op params = do nums <- traverse conv params
                            pure $ Num (foldl1 op nums)

boolBinop : Convert a => (a -> a -> Bool) -> List LispVal ->
                         Either LispError LispVal
boolBinop op [x, y] = do x' <- conv x
                         y' <- conv y
                         pure $ Bool (op x' y')
boolBinop _ args = Left $ NumArgs 2 args

car : List LispVal -> Either LispError LispVal
car [List (x :: xs)] = Right x
car [Dotted (x :: xs) _] = Right x
car [badArg] = Left $ TypeMisMatch "pair" badArg
car badArgList = Left $ NumArgs 1 badArgList

cdr : List LispVal -> Either LispError LispVal
cdr [List [_]] = Right $ Nil
cdr [List (_ :: xs)] = Right $ List xs
cdr [Dotted [_] x] = Right x
cdr [Dotted (_ :: xs) x] = Right $ Dotted xs x
cdr [badArg] = Left $ TypeMisMatch "pair" badArg
cdr badArgList = Left $ NumArgs 1 badArgList

cons : List LispVal -> Either LispError LispVal
cons [x, Nil] = Right $ List [x]
cons [x, List xs] = Right $ List (x :: xs)
cons [x, Dotted xs xlast] = Right $ Dotted (x :: xs) xlast
cons [x, y] = Right $ Dotted [x] y
cons badArgList = Left $ NumArgs 2 badArgList

eqv : List LispVal -> Either LispError LispVal
eqv [Bool b1, Bool b2] = Right $ Bool (b1 == b2)
eqv [Num n1, Num n2] = Right $ Bool (n1 == n2)
eqv [Str s1, Str s2] = Right $ Bool (s1 == s2)
eqv [Atom a1, Atom a2] = Right $ Bool (a1 == a2)
eqv [Nil, Nil] = Right $ Bool True
eqv [List [], List []] = Right $ Bool True
eqv [List [], List _] = Right $ Bool False
eqv [List _, List []] = Right $ Bool False
eqv [List (x :: xs), List (y :: ys)]
    = do Bool True <- eqv [x, y] | _ => pure (Bool False)
         eqv [List xs, List ys]
eqv [Dotted xs x, Dotted ys y]
    = eqv [List (xs ++ [x]), List (ys ++ [y])]
eqv [_, _] = Right $ Bool False
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

-- Primitive IO Functions
public export
IOFunction : Type
IOFunction = List LispVal -> EitherT LispError IO LispVal

applyProc : IOFunction
applyProc [fn, List args] = apply fn args
applyProc (fn :: args) = apply fn args
applyProc _ = left $ Default "apply: expected 2 or more arguments"

makePort : Mode -> IOFunction
makePort mode [Str filename]
  = do Right file <- lift $ openFile filename mode
        | Left err => left (Default $ "can't open file " ++ filename ++
                            " " ++ show err)
       pure (Port file)
makePort _ [val] = left $ TypeMisMatch "string" val
makePort _ expr = left $ NumArgs 1 expr

closePort : IOFunction
closePort [Port file] = do lift $ closeFile file
                           pure $ Bool True 
closePort _ = pure $ Bool False

readProc : IOFunction 
readProc [] = readProc [Port stdin]
readProc [Port port] = do Right str <- lift (fGetLine port)
                            | Left err => left (Default (show err))
                          liftEither $ readExpr str
readProc [val] = left $ TypeMisMatch "port" val
readProc xs = left $ NumArgs 1 xs

writeProc : IOFunction
writeProc [obj] = writeProc [obj, Port stdout]
writeProc [obj, Port file] = do Right _ <- lift $ fPutStr file (show obj)
                                  | Left _ => pure (Bool False)
                                pure (Bool True)
writeProc _ = left $ Default "write: Invalid arguments"

readContents : IOFunction
readContents [Str filename]
  = do Right str <- lift $ readFile filename
        | Left err => left (Default $ show err)
       pure $ Str str
readContents [val] = left $ TypeMisMatch "string" val
readContents xs = left $ NumArgs 1 xs

readAll : IOFunction
readAll [Str filename] = map List $ load filename
readAll [val] = left $ TypeMisMatch "string" val
readAll expr = left $ NumArgs 1 expr

ioPrimitives : List (String, IOFunction)
ioPrimitives = [("apply", applyProc),
                ("open-input-file", makePort Read),
                ("open-output-file", makePort WriteTruncate),
                ("close-input-port", closePort),
                ("close-output-port", closePort),
                ("read", readProc),
                ("write", writeProc),
                ("read-contents", readContents),
                ("read-all", readAll)]

nullEnv : IO EnvCtx
nullEnv = newIORef []

export
primitiveBindings : IO EnvCtx
primitiveBindings
  = let mkPrimFunctions = \(var, func) => (var, Function func)
        mkIOFunctions = \(var, func) => (var, IOFunc func) in
        nullEnv >>= flip bindVars (map mkPrimFunctions primitives
                                  ++ map mkIOFunctions ioPrimitives)

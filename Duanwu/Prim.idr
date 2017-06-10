module Duanwu.Prim

import Duanwu.LispVal
import Duanwu.Parser
import Duanwu.Helper
import Duanwu.Eval
import Data.IORef
import Control.Monad.Trans

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

-- Primitive IO Functions
public export
IOFunction : Type
IOFunction = List LispVal -> EitherT LispError IO LispVal

applyProc : IOFunction
applyProc [fn, LispList args] = apply fn args
applyProc (fn :: args) = apply fn args
applyProc _ = left $ Default "apply: expected 2 or more arguments"

makePort : Mode -> IOFunction
makePort mode [LispStr filename]
  = do Right file <- lift $ openFile filename mode
        | Left err => left (Default $ "can't open file " ++ filename ++
                            " " ++ show err)
       pure (Port file)
makePort _ [val] = left $ TypeMisMatch "string" val
makePort _ expr = left $ NumArgs 1 expr

closePort : IOFunction
closePort [Port file] = do lift $ closeFile file
                           pure $ LispBool True 
closePort _ = pure $ LispBool False

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
                                  | Left _ => pure (LispBool False)
                                pure (LispBool True)
writeProc _ = left $ Default "write: Invalid arguments"

readContents : IOFunction
readContents [LispStr filename]
  = do Right str <- lift $ readFile filename
        | Left err => left (Default $ show err)
       pure $ LispStr str
readContents [val] = left $ TypeMisMatch "string" val
readContents xs = left $ NumArgs 1 xs

readAll : IOFunction
readAll [LispStr filename] = map LispList $ load filename
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

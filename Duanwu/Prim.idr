module Duanwu.Prim

import Duanwu.LispVal
import Duanwu.Parser
import Control.ST
import Control.ST.FileIO

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
IOResult : (Type -> Type) -> Type -> Type
IOResult m a = ST m (Either LispError a) [] 

makePort : FileIO m => Mode -> List LispVal -> IOResult m LispVal
makePort mode [Str filename]
  = do Right file <- openFile filename mode
        | Left e => err (Default $ "can't open file " ++ filename ++
                             " " ++ show e)
       ok (Port file)
makePort _ [val] = err $ TypeMisMatch "string" val
makePort _ expr = err $ NumArgs 1 expr

closePort : FileIO m => List LispVal -> IOResult m LispVal
closePort [Port file] = do closeFile file
                           ok $ Bool True 
closePort _ = ok $ Bool False

readProc : FileIO m => List LispVal -> IOResult m LispVal 
readProc [] = readProc [Port stdin]
readProc [Port port] = do Right str <- fGetLine port
                            | Left e => err (Default (show e))
                          pure $ readExpr str
readProc [val] = err $ TypeMisMatch "port" val
readProc xs = err $ NumArgs 1 xs

writeProc : FileIO m => List LispVal -> IOResult m LispVal
writeProc [obj] = do r <- fPutStr stdout (show obj)
                     ok . Bool $ either (const False) (const True) r
writeProc [obj, Port file] = do r <- fPutStr file (show obj)
                                ok . Bool $ either (const False) (const True) r
writeProc _ = err $ Default "write: Invalid arguments"

readContents : FileIO m => List LispVal -> IOResult m LispVal
readContents [Str filename]
  = do Right str <- readFile filename
        | Left e => err (Default $ show e)
       ok $ Str str
readContents [val] = err $ TypeMisMatch "string" val
readContents xs = err $ NumArgs 1 xs

export
load : FileIO m => String -> ST m (Either LispError (List LispVal)) []
load filename = do Right str <- readFile filename
                    | Left e => err (Default $ show e)
                   pure $ readExprList str

readAll : FileIO m => List LispVal -> IOResult m LispVal
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
runPrim : FileIO m =>
          PrimFun -> List LispVal -> ST m (Either LispError LispVal) []
runPrim Car  = pure . car 
runPrim Cdr  = pure . cdr
runPrim Cons = pure . cons 
runPrim Eqv  = pure . eqv 
runPrim Add  = pure . numericBinop (+) 
runPrim Sub  = pure . numericBinop (-) 
runPrim Mult = pure . numericBinop (*) 
runPrim Div = pure . numericBinop div 
runPrim Mod = pure . numericBinop mod 
runPrim And = pure . boolBinop (\x, y => x && y) 
runPrim Or  = pure . boolBinop (\x, y => x || y) 
runPrim EQ  = pure . boolBinop {a = Integer} (==) 
runPrim LT  = pure . boolBinop {a = Integer} (<) 
runPrim GT  = pure . boolBinop {a = Integer} (>) 
runPrim NE  = pure . boolBinop {a = Integer} (/=) 
runPrim LTE = pure . boolBinop {a = Integer} (<=) 
runPrim GTE = pure . boolBinop {a = Integer} (>=) 
runPrim StrEq  = pure . boolBinop {a = String} (==) 
runPrim StrLT  = pure . boolBinop {a = String} (<) 
runPrim StrGT  = pure . boolBinop {a = String} (>) 
runPrim StrLTE = pure . boolBinop {a = String} (<=) 
runPrim StrGTE = pure . boolBinop {a = String} (>=) 
runPrim OpenInputFile   = makePort Read  
runPrim OpenOutputFile  = makePort WriteTruncate 
runPrim CloseInputFile  = closePort 
runPrim CloseOutputFile = closePort 
runPrim Read  = readProc 
runPrim Write = writeProc 
runPrim ReadContents  = readContents 
runPrim ReadAll  = readAll 
runPrim Apply = const $ err $ Panic "Apply: PrimFun should not run in runPrim"

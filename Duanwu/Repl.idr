module Duanwu.Repl 

import Duanwu.LispVal
import Duanwu.Parser
import Duanwu.Eval
import Data.IORef
import Duanwu.Helper
import Control.Monad.Trans

parseAndEval : EnvCtx -> String -> Eval LispVal
parseAndEval env input = liftEither (readExpr input) >>= eval env 

eval1 : String -> Eval LispVal
eval1 input = lift primitiveBindings >>= flip parseAndEval input

evalAndPrint : String -> IO ()
evalAndPrint = eitherT printLn printLn . eval1

runRepl : IO ()
runRepl = do putStrLn "Lisp Repl"
             env <- primitiveBindings
             repl env
  where
  repl : EnvCtx -> IO ()
  repl env
    = do putStr ">"
         "quit" <- getLine
           | input => do Right val <- runEitherT (parseAndEval env input) 
                          | Left err => do printLn err; repl env
                         printLn val
                         repl env
         pure ()

export
main : IO ()
main
  = do args <- getArgs
       case args of
            [cmd] => runRepl 
            [cmd, arg] => evalAndPrint arg
            _ => putStrLn "Program takes only 0 or 1 argument"


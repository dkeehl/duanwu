module Duanwu.Repl 

import Duanwu.LispVal
import Duanwu.Parser
import Duanwu.Eval
import Duanwu.Prim

parseAndEval : EnvCtx -> String -> Eval LispVal
parseAndEval env input = liftEither (readExpr input) >>= eval env 

evalAndPrint : List String -> IO ()
evalAndPrint [] = pure ()
evalAndPrint (filename :: args)
  = do env <- primitiveBindings
       let args' = LispList $ map LispStr args 
       env' <- bindVars env [("args", args')]
       let expr = LispList [LispAtom "load", LispStr filename]
       eitherT printLn printLn $ eval env' expr

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
main = do args <- getArgs
          case args of
               [cmd] => runRepl 
               (cmd :: args) => evalAndPrint args
               [] => pure () -- impossible


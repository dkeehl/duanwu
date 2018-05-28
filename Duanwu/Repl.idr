module Duanwu.Repl 
import Duanwu.LispVal
import Duanwu.Parser
import Duanwu.Eval
import Duanwu.Prim
import Effects
import Effect.Env
import Effect.Exception
import Effect.FileIO
import Effect.StdIO

parseAndEval : EnvRef LispVal -> String ->
               Eff (Either LispError LispVal) [ENV LispVal, EXCEPTION Panic, FILE_IO]
parseAndEval env input = do case readExpr input of
                                 Right val => eval env val
                                 Left e => err e

evalAndPrint : List String ->
               Eff () [ENV LispVal, EXCEPTION Panic, FILE_IO, STDIO]
evalAndPrint [] = pure ()
evalAndPrint (filename :: args)
  = do env <- initEnv primitives
       let args' = List $ map Str args 
       env' <- local env [("args", args')]
       let expr = List [Atom "load", Str filename]
       Right val <- eval env' expr | Left e => printLn e
       printLn val

interact : Eff () [ENV LispVal, EXCEPTION Panic, FILE_IO, STDIO]
interact = do putStrLn "Lisp Repl"
              env <- initEnv primitives
              repl env
  where
  repl : EnvRef LispVal -> Eff () [ENV LispVal, EXCEPTION Panic, FILE_IO, STDIO]
  repl env
    = do putStr ">"
         "quit" <- getStr
           | input => do Right val <- parseAndEval env input
                          | Left err => do printLn err; repl env
                         printLn val
                         repl env
         pure ()

export
main : IO ()
main = do args <- getArgs
          case args of
               [cmd] => run interact
               (cmd :: args) => run $ evalAndPrint args
               [] => pure () -- unreachable


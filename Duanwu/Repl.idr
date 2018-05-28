module Duanwu.Repl 

import Duanwu.LispVal
import Duanwu.Parser
import Duanwu.Eval
import Duanwu.Prim
import Control.ST
import Control.ST.Envir
import Control.ST.FileIO

parseAndEval : (Envir LispVal m, FileIO m) =>
               EnvRef LispVal -> String -> ST m (Either LispError LispVal) []
parseAndEval env input = do case readExpr input of
                                 Right val => eval env val
                                 Left e => err e

export
evalAndPrint : (Envir LispVal m, FileIO m, ConsoleIO m) =>
               List String -> ST m () []
evalAndPrint [] = pure ()
evalAndPrint (filename :: args)
  = do env <- initEnv primitives
       let args' = List $ map Str args 
       env' <- local env [("args", args')]
       let expr = List [Atom "load", Str filename]
       Right val <- eval env' expr | Left e => printLn e
       printLn val

export
interact : (Envir LispVal m, FileIO m, ConsoleIO m) => STLoop m () []
interact = do putStrLn "Lisp Repl"
              env <- initEnv primitives
              repl env
  where
  repl : (Envir LispVal m, FileIO m, ConsoleIO m) =>
         EnvRef LispVal -> STLoop m () []
  repl env
    = do putStr ">"
         "quit" <- getStr
           | input =>
                do Right val <- parseAndEval env input
                    | Left e => do printLn e
                                   case e of
                                     Panic _ => pure ()
                                     _ => repl env
                   printLn val
                   repl env

         pure ()


module Duanwu.Repl 

import Duanwu.LispVal
import Duanwu.Parser
import Duanwu.Eval
import Control.ST
import Data.SortedMap
{-
evalAndPrint : (Exception m LispError, ConsoleIO m) => String -> ST m () []
evalAndPrint input = liftEither (readExpr input) >>= eval1 >>= printLn
-}

parseAndEval : (env : Var) -> String ->
               Eval m LispVal [env ::: State EnvCtx]
parseAndEval env input = case readExpr input of
                              Left err => pureL err
                              Right expr => eval env expr 

eval1 : String -> Eval m LispVal []
eval1 input = do env <- new primitiveBindings
                 Right val <- parseAndEval env input
                  | Left err => do delete env; pureL err
                 delete env
                 pureR val

evalAndPrint : String -> IO ()
evalAndPrint = either printLn printLn . runPure . eval1

repl : ConsoleIO m => (init : EnvCtx) -> STLoop m () []
repl init = do env <- new init
               putStr "Lisp >"
               "quit" <- getStr
                 | input => do val <- parseAndEval env input
                               either printLn printLn val
                               current <- read env
                               delete env
                               repl current
               delete env
               putStrLn "Bye"
               pure ()

{-
repl' : ConsoleIO m => (env : Var) ->
        STransLoop m () [env ::: EnvCtx] (const [])
repl' env = do putStr "Lisp >"
               "quit" <- getStr
                 | input => do val <- parseAndEval env input
                               either printLn printLn val
                               repl' env 
               delete env
               putStrLn "Bye"
               pure ()

runRepl : ConsoleIO m => STransLoop m () [] (const [])
runRepl = new empty >>= Repl.repl'
-}

export
main : IO ()
main
  = do args <- getArgs
       case args of
            [cmd] => runLoop forever (repl primitiveBindings) $
                     putStr "Out of fuel"
            [cmd, arg] => evalAndPrint arg
            _ => putStrLn "Program takes only 0 or 1 argument"


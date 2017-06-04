module Duanwu.Repl 

import Duanwu.LispVal
import Duanwu.Parser
import Duanwu.Eval

evalAndShow : String -> String
evalAndShow input
  = either show show result
  where result : Either LispError LispVal
        result = readExpr input >>= eval

evalAndPrint : String -> IO ()
evalAndPrint = putStrLn . evalAndShow

runRepl : IO ()
runRepl = replWith () "Lisp>>>" runReplAux
  where 
    runReplAux : () -> String -> Maybe (String, ())
    runReplAux _ "quit" = Nothing
    runReplAux _ input = Just (evalAndShow input ++ "\n", ())

export
mainloop : IO ()
mainloop = do args <- getArgs
              case args of
                   [cmd] => runRepl 
                   [cmd, arg] => evalAndPrint arg
                   _ => putStrLn "Program takes only 0 or 1 argument"

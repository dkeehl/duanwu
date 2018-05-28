module Main

import Duanwu.LispVal
import Duanwu.Parser
import Duanwu.Prim
import Duanwu.Repl
import Control.ST
import Control.ST.Envir
import Control.ST.FileIO

main : IO ()
main = do args <- getArgs
          case args of
               [cmd] => runLoop forever Repl.interact (pure ())
               (cmd :: args) => run $ Repl.evalAndPrint args
               [] => pure () -- unreachable


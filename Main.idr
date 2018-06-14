module Main

import Duanwu.LispVal
import Duanwu.Repl
import Effects
import Effect.FileIO
import Effect.Env
import Effect.StdIO

main : IO ()
main = do args <- getArgs
          case args of
               [cmd] => run interact
               (cmd :: args) => run $ evalAndPrint args
               [] => assert_unreachable


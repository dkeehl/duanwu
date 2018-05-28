module Effect.FileIO

import Effects

%default total
%access public export

data FileIO : Effect where
     Open : (fname: String) -> (m: Mode) -> sig FileIO (Either FileError File)
     Close :    File                     -> sig FileIO () 
     GetLine :  File                     -> sig FileIO (Either FileError String)
     PutStr :   File -> String           -> sig FileIO (Either FileError ())
     ReadFile : (fpath: String)          -> sig FileIO (Either FileError String)

FILE_IO : EFFECT
FILE_IO = MkEff () FileIO

Handler FileIO IO where
  handle () (Open fname m) k = do r <- openFile fname m; k r ()
  handle () (Close f)      k = do closeFile f; k () ()
  handle () (GetLine f)    k = do s <- fGetLine f; k s ()
  handle () (PutStr f s)   k = do r <- fPutStr f s; k r ()
  handle () (ReadFile f)   k = do s <- readFile f; k s ()

openFile : (fname: String) -> (m: Mode) -> Eff (Either FileError File) [FILE_IO]
openFile fname m = call $ Open fname m

closeFile : File -> Eff () [FILE_IO]
closeFile f = call $ Close f

fGetLine : File -> Eff (Either FileError String) [FILE_IO]
fGetLine f = call $ GetLine f

fPutStr : File -> String -> Eff (Either FileError ()) [FILE_IO]
fPutStr f s = call $ PutStr f s

readFile : (fpath: String) -> Eff (Either FileError String) [FILE_IO]
readFile fpath = call $ ReadFile fpath


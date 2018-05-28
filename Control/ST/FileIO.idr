module Control.ST.FileIO

import Control.ST

%default total
%access public export

interface FileIO (m: Type -> Type) where
  openFile : (fname: String) -> Mode -> ST m (Either FileError File) []
  closeFile : File -> ST m () []
  fGetLine : File -> ST m (Either FileError String) []
  fPutStr : File -> String -> ST m (Either FileError ()) []
  readFile : (fpath: String) -> ST m (Either FileError String) []

FileIO IO where
  openFile fname m = lift $ openFile fname m
  closeFile f = lift $ closeFile f
  fGetLine f = lift $ fGetLine f
  fPutStr f s = lift $ fPutStr f s
  readFile fpath = lift $ readFile fpath


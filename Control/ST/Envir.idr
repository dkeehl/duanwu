module Control.ST.Envir

import Control.ST
import Data.IORef

%default total
%access public export

data EnvRef : Type -> Type where
     MkRef : IORef (List (String, IORef a)) -> EnvRef a

interface Envir a (m: Type -> Type) | m where
  initEnv :   List (String, a)             -> ST m (EnvRef a) []
  getVar :    EnvRef a -> String           -> ST m (Maybe a) []
  setVar :    EnvRef a -> String -> a      -> ST m Bool []
  defineVar : EnvRef a -> String -> a      -> ST m () []
  local :     EnvRef a -> List (String, a) -> ST m (EnvRef a) []

private
addBinding : (String, a) -> IO (String, IORef a)
addBinding (k, v) = do ref <- newIORef v; pure (k, ref)

Envir a IO where
  initEnv l = lift $ traverse addBinding l >>= newIORef >>= pure . MkRef

  getVar (MkRef e) var = lift $
    do case lookup var !(readIORef e) of
            Nothing => pure Nothing
            Just ref => map Just (readIORef ref)

  setVar (MkRef e) var val = lift $
    do case lookup var !(readIORef e) of
            Nothing => pure False
            Just ref => do writeIORef ref val 
                           pure True

  defineVar (MkRef e) var val = lift $
    do case lookup var !(readIORef e) of
            Nothing => do ref <- newIORef val
                          modifyIORef e ((var, ref) ::)
            Just ref => writeIORef ref val

  local (MkRef e) l = lift $
    do env <- readIORef e
       let bindings = traverse addBinding l
       ref <- newIORef !(liftA (++ env) bindings)
       pure (MkRef ref)

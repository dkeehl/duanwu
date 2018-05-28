module Effect.Env

import Effects
import Data.IORef
import Control.IOExcept

%default total
%access public export

data EnvRef : Type -> Type where
     MkRef : IORef (List (String, IORef a)) -> EnvRef a

data Env : Type -> Effect where
     Init :   List (String, a)             -> sig (Env a) (EnvRef a)
     Get :    EnvRef a -> String           -> sig (Env a) (Maybe a)
     Set :    EnvRef a -> String -> a      -> sig (Env a) Bool
     Define : EnvRef a -> String -> a      -> sig (Env a) ()
     Local :  EnvRef a -> List (String, a) -> sig (Env a) (EnvRef a)

ENV : Type -> EFFECT
ENV a = MkEff () (Env a)

private
addBinding : (String, a) -> IO (String, IORef a)
addBinding (k, v) = do ref <- newIORef v; pure (k, ref)

Handler (Env a) IO where
  handle () (Init l) k = do ref <- newIORef !(traverse addBinding l)
                            k (MkRef ref) ()

  handle () (Get (MkRef e) var) k =
    do case lookup var !(readIORef e) of
            Nothing => k Nothing ()
            Just ref => k (Just !(readIORef ref)) ()

  handle () (Set (MkRef e) var val) k =
    do case lookup var !(readIORef e) of
            Nothing => k False ()
            Just ref => do writeIORef ref val 
                           k True ()

  handle () (Define (MkRef e) var val) k =
    do case lookup var !(readIORef e) of
              Nothing => do ref <- newIORef val
                            modifyIORef e ((var, ref) ::)
              Just ref => writeIORef ref val
       k () ()

  handle () (Local (MkRef e) l) k =
    do env <- readIORef e
       let bindings = traverse addBinding l
       ref <- newIORef !(liftA (++ env) bindings)
       k (MkRef ref) ()

initEnv : List (String, a) -> Eff (EnvRef a) [ENV a]
initEnv l = call $ Init l

getVar : EnvRef a -> String -> Eff (Maybe a) [ENV a]
getVar e var = call $ Get e var

setVar : EnvRef a -> String -> a -> Eff Bool [ENV a]
setVar e var val = call $ Set e var val

defineVar : EnvRef a -> String -> a -> Eff () [ENV a]
defineVar e var val = call $ Define e var val

local : EnvRef a -> List (String, a) -> Eff (EnvRef a) [ENV a]
local e l = call $ Local e l


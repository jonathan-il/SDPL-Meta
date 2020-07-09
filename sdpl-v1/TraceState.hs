module TraceState where

import qualified Data.Map as M
import SDPLTerms
import ST 
import Err
import Control.Monad.Trans

-- *********************
-- Some stateful stuff
-- *********************

data TState a = TS {
    locals :: M.Map String (ClosedVal a),
    seedName :: String,
    freshName :: Int
}

freshVar :: Monad m => ST (TState a) m String 
freshVar = do 
  seed <- getST  seedName 
  counter <- getST freshName 
  -- invariant seed++(show counter) have never been seen 
  let fvar = seed ++ (show counter)
  updateST $ \s -> s {freshName = counter + 1}
  return fvar

getLocals :: Monad m => ST (TState a) m (M.Map String (ClosedVal a))
getLocals = getST locals

setLocals :: Monad m => (M.Map String (ClosedVal a)) -> ST (TState a) m ()
setLocals newLocals = updateST $ \s -> s {locals = newLocals}

-- We could do something like a typeclass HasMap a that has a function a -> M.Map b c... then we could do many of these functions abstractly once and for all...

-- Side effect: this will overwrite the current variable entirely
setVar :: Monad m => String -> (ClosedVal a) -> ST (TState a) m ()
setVar x val = do 
  locs <- getLocals 
  let newLocs = M.insert x val locs
  setLocals newLocs

getVar :: String -> ST (TState a) Err (ClosedVal a)
getVar x = do 
  loc <- getLocals 
  case M.lookup x loc of
    Nothing -> lift $ Fail $ "error: This is a bug.  Variable " ++ x ++ " was looked up but not found in environment"
    Just val -> return val 

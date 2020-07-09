module InterpreterState where


import SDPLTerms
import Err 


-- Monad transformer imports
import Control.Monad.Trans 
import qualified Control.Monad.Trans.State.Strict as State
import qualified Data.Map as M

type ST s m a = State.StateT s m a

-- we can generalize this to arbitrary v later
type VarMap a = M.Map Int (ClosedVal a)

data IState a = IState {
    funMap :: ProgI a,
    locals :: VarMap a,
    stackOfLocals :: [VarMap a],
    freshCounter :: Int
}

-- ****************************
-- State manipulation stuff
-- ****************************

freshVar :: Monad m => ST (IState a) m Int 
freshVar = do 
    fvar <- State.gets freshCounter 
    -- invariant seed++(show counter) have never been seen 
    -- possible profiling point is whether modify' is worth it over modify
    State.modify' $ \s -> s {freshCounter = succ fvar}
    return fvar 

{-# INLINABLE freshVar #-}


getFunMap :: Monad m => ST (IState a) m (ProgI a)
getFunMap = State.gets funMap

{-# INLINABLE getFunMap #-}


setFunMap :: Monad m => (ProgI a) -> ST (IState a) m ()
setFunMap newFuns = State.modify $ \s -> s {funMap = newFuns}

{-# INLINABLE setFunMap #-}



getLocals :: Monad m => ST (IState  a) m (VarMap a)
getLocals = State.gets locals

{-# INLINABLE getLocals #-}

setLocals :: Monad m => VarMap a -> ST (IState  a) m ()
setLocals newLocals = State.modify $ \s -> s {locals = newLocals}

{-# INLINABLE setLocals #-}

getStack :: Monad m => ST (IState  a) m [VarMap a]
getStack = State.gets stackOfLocals

{-# INLINABLE getStack #-}

setStack :: Monad m => [VarMap a] -> ST (IState a) m ()
setStack newStack = State.modify $ \s -> s {stackOfLocals = newStack}

{-# INLINABLE setStack #-}


-- push locals onto the stack, i.e. before a function call.
pushLocals :: Monad m => ST (IState a) m ()
pushLocals = do 
  loc <- getLocals 
  stack <- getStack 
  setLocals M.empty 
  setStack (loc:stack)

{-# INLINABLE pushLocals #-}

-- Precondition: must be called after a push
-- Side effect: discards the current locals 
popLocals :: ST (IState a) Err () 
popLocals = do 
  s <- getStack 
  case s of 
    (loc:stack) -> do 
      setStack stack 
      setLocals loc -- here we overwrite the locals, whatever they were -- this should only be called when exiting a function body. 
    _ -> lift $ Fail $ "error: Pop was called before a push"

{-# INLINABLE popLocals #-}

-- Side effect: this will overwrite the current variable entirely
setVar :: Monad m => Int -> (ClosedVal a) -> ST (IState  a) m ()
setVar x val = do 
  locs <- getLocals 
  let newLocs = M.insert x val locs
  setLocals newLocs

{-# INLINABLE setVar #-}

getVar :: Int -> ST (IState  a) Err (ClosedVal a)
getVar x = do 
  loc <- getLocals 
  case M.lookup x loc of
    Nothing -> lift $ Fail $ "error: This is a bug.  Variable " ++ show x ++ " was looked up but not found in the environment"
    Just val -> return val 

{-# INLINABLE getVar #-}


getFun :: String -> ST (IState  a) Err (FuncIClosure a)
getFun name = do 
  fm <- getFunMap 
  case M.lookup name fm of 
    Nothing -> lift $ Fail $ name ++ " not defined in the program"
    Just myFun -> return myFun

{-# INLINABLE getFun #-}

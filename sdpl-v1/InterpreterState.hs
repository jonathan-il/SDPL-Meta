module InterpreterState where

import SDPLTerms

import ST 
import Err

import Control.Monad.Trans

import qualified Data.Map as M

type VarMap a = M.Map String (ClosedVal a)
-- type FunMap s p a = M.Map String (Func s p a) -- this contains the closure of the function
-- data InterpreterState s p a = IS {
data IState s p a = IState {
    funMap :: Prog s p a,
    locals  :: VarMap a,
    stackOfLocals :: [VarMap a],
    freshVarSeed :: String,
    freshCounter :: Int
}

-- ****************************
-- State manipulation stuff
-- ****************************
-- Again this should be redone with the (HasMap s,HasFresh s, etc) so that we can get around duplicating so much coding.
freshVar :: Monad m => ST (IState s p a) m String 
freshVar = do 
  seed <- getST  freshVarSeed 
  counter <- getST freshCounter 
  -- invariant seed++(show counter) have never been seen 
  let fvar = seed ++ (show counter)
  updateST $ \s -> s {freshCounter = counter + 1}
  return fvar

getFunMap :: Monad m => ST (IState s p a) m  (Prog s p a)
getFunMap = getST funMap

setFunMap :: Monad m => (Prog s p a) -> ST (IState s p a) m ()
setFunMap newFuns = updateST $ \s -> s {funMap = newFuns}

getLocals :: Monad m => ST (IState s p a) m (VarMap a)
getLocals = getST locals

setLocals :: Monad m => VarMap a -> ST (IState s p a) m ()
setLocals newLocals = updateST $ \s -> s {locals = newLocals}

getStack :: Monad m => ST (IState s p a) m [VarMap a]
getStack = getST stackOfLocals

setStack :: Monad m => [VarMap a] -> ST (IState s p a) m ()
setStack newStack = updateST $ \s -> s {stackOfLocals = newStack}


-- push locals onto the stack, i.e. before a function call.
pushLocals :: Monad m => ST (IState s p a) m ()
pushLocals = do 
  loc <- getLocals 
  stack <- getStack 
  setLocals M.empty 
  setStack (loc:stack)

-- Precondition: must be called after a push
-- Side effect: discards the current locals 
popLocals :: ST (IState s p a) Err () 
popLocals = do 
  s <- getStack 
  case s of 
    (loc:stack) -> do 
      setStack stack 
      setLocals loc -- here we overwrite the locals, whatever they were -- this should only be called when exiting a function body. 
    _ -> lift $ Fail $ "error: Pop was called before a push"

-- Side effect: this will overwrite the current variable entirely
setVar :: Monad m => String -> (ClosedVal a) -> ST (IState s p a) m ()
setVar x val = do 
  locs <- getLocals 
  let newLocs = M.insert x val locs
  setLocals newLocs

getVar :: String -> ST (IState s p a) Err (ClosedVal a)
getVar x = do 
  loc <- getLocals 
  case M.lookup x loc of
    Nothing -> lift $ Fail $ "error: This is a bug.  Variable " ++ x ++ " was looked up but not found in the environment"
    Just val -> return val 

getFun :: String -> ST (IState s p a) Err (FuncClosure s p a)
getFun name = do 
  fm <- getFunMap 
  case M.lookup name fm of 
    Nothing -> lift $ Fail $ name ++ " not defined in the program"
    Just myFun -> return myFun
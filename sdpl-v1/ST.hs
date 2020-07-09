{-# LANGUAGE Strict, StrictData #-}

module ST where

import Control.Monad.Trans
import Control.Monad

{- 
There are lots of issues when using state this way.  We should be using Control.Monad.Trans.State.
-}
data ST s m a = ST !(s -> m (a,s)) --{!runST :: s -> m (a,s)}

runST :: ST s m a -> s -> m (a,s)
runST (ST f) = f

type State s a = ST s K a

runState :: State s a -> s -> (a,s)
runState comp initstate = 
    let
        K x = runST comp initstate
    in 
        x

runStateVal :: State s a -> s -> a
runStateVal comp = fst . runState comp
    -- evalState comp = fst . runState comp

runSTVal :: Functor m => ST s m a -> s -> m a
runSTVal comp s = fmap fst $ runST comp s

{-
The truth is, I shouldn't be writing this module.  We should
be using State from Control.Monad.Trans.State.
-}
instance Monad m => Monad (ST s m) where 
    return a = ST $ \s -> return (a,s)
    st >>= f = ST $ \s -> do 
        (a1,s1) <- runST st s 
        (a2,s2) <- runST (f a1) s1
        return $ (a2,s2)

instance Monad m => Applicative (ST s m) where
    pure a = ST $ \s -> return (a,s)
    f <*> x = do 
        f' <- f 
        f' <$> x


instance Monad m => Functor (ST s m) where 
    -- fmap :: (a -> b) -> ST s m a -> ST s m b
    fmap f s = f <$> s

instance MonadTrans (ST s) where
    lift m = ST $ \s -> do 
        a <- m 
        return (a,s)

{-
Often you want to retrieve the state, or some part of it.  We allow filtering the
part returned through a function g.
-}
getST :: Monad m => (s -> a) -> ST s m a 
getST g = ST $ \s -> return (g s, s)

updateST :: Monad m => (s -> s) -> ST s m () 
updateST u = ST $ \s -> return ((),u s)

setST :: Monad m => s -> ST s m ()
setST s = ST $ \s' -> return ((), s)



data K x = K x 

instance Functor K where 
    fmap f (K x) = K (f x)

instance Applicative K where
    pure = K
    -- <*> : f (a -> b) -> f a -> f b
    (K f) <*> (K x) = K (f x)

instance Monad K where 
    return = K 
    -- >>= : m a -> (a -> m b) -> m b
    (K x) >>= f = f x

test :: ST Int Maybe Int
test = lift (Just 4) 
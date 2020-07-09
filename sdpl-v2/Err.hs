{-
The standard Error module Either also doesn't 
do anything with inlines or optimizations. 

In a real world version it might be better to 
do something like use either and create more 
customized Exception types, and use MonadThrow 
to abstract these exceptions away.  But if we 
did that, then it would be really nice to be able 
to know what kind of error is being thrown.  But for now 
returning error messages all day is fine.
-}

module Err where

data Err a = Fail String | Ok a 

instance Show a => Show (Err a) where
    show (Fail msg) = msg 
    show (Ok x) = show x 

instance Functor Err where 
    fmap _ (Fail msg) = Fail msg 
    fmap f (Ok x) = Ok (f x)

instance Applicative Err where
    pure = Ok 
    -- <*> : f (a -> b) -> f a -> f b 
    _ <*> (Fail msg) = Fail msg 
    (Ok f) <*> (Ok x) = Ok (f x)

instance Monad Err where 
    return = Ok
    -- m a -> (a -> m b) -> m b
    (Fail msg) >>= _ = Fail msg 
    (Ok x) >>= f = f x
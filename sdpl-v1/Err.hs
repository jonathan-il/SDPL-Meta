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
{-# LANGUAGE GADTs #-}

module DelayMonad where

data Delay a = Now a | Later (Delay a)

never :: Delay a 
never = Later never 

race :: Delay a -> Delay a -> Delay a 
race (Now a) _ = Now a 
race (Later _) (Now a) = Now a
race (Later f) (Later g) = Later (race f g)

instance Functor Delay where 
    -- f : a -> b 
    fmap f d = case d of 
        Now x -> Now (f x)
        Later d -> Later (fmap f d)

instance Applicative Delay where 
    -- pure :: a -> f a
    pure = Now 
    -- <*> :: f (a -> b) -> f a -> f b 
    (Now f) <*> (Now x) = Now (f x)
    (Later d) <*> (Now x) = d <*> (Now x)
    (Now f) <*> (Later d) = (Now f) <*> d 
    (Later df) <*> (Later dx) = df <*> dx

instance Monad Delay where 
    -- m a -> (a -> m b) -> m b 
    (Now x) >>= f = f x 
    (Later d) >>= f = Later (d >>= f)


-- a -> b + a
--------------
-- a -> b
trace :: (a -> Delay (Either b a)) -> a -> Delay b
trace f x = do 
    waited <- f x 
    case waited of 
        Left b -> Now b 
        -- Right a -> trace f a also types, but we want them to wait for it
        Right a -> Later $ trace f a


data Stream a = Stream {head :: a, tail :: Stream a}

-- The idea here is that we take a mealy machine step, i.e. a function from states and a-values to states and b-values, some initital state s, and produce a delayed state, or the next one 
-- in the computation, as well as the value output.  You can also think of this is as the 0th unrolling of the causal computation associated to the mealy step and the initial state.
-- Normally, you throw discard these steps in the unrolling, but I want to try to keep them around as a delayed state and see if that helps.
makeDelayFromMealyStep :: ((s,a) -> (s,b)) -> s -> (a -> (Delay s, b))
makeDelayFromMealyStep m i = 
    let 
        -- m' 
        m' = curry m i
    in  \a -> let (i',b) = m' a in (Later (Now i'),b)

-- note that uncurry2 == f . uncurry
uncurry2 :: (a -> b -> c -> d) -> a -> ((b,c) -> d)
uncurry2 = \f x -> uncurry (f x)
-- Now we'll try to lift a mealy step directly to another mealy step, but with a delay
-- we are still thinking here of the s being passed in as being the initial state. 
makeDelayedStepFromStep :: ((s,a) -> (s,b)) -> (s,a) -> (Delay s, b)
makeDelayedStepFromStep = uncurry . makeDelayFromMealyStep

-- Let's define how to chain two delayed steps together
-- The idea is that the number of delays tells you how much unwinding is needed.
makeDelayedStepFromDelayedStep 
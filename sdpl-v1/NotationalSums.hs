module NotationalSums where 

import Data.Monoid
import SDPLTerms
import TraceState
import qualified InterpreterState as IS 
import ST 

{-
We need to construct 0 and addition given type information.  This is why the 
reverse derivative needs to carry the type around with it at all times.
-}
makeZeroVal :: Monoid a => LType -> Val a 
makeZeroVal typ = case typ of 
    Unit -> VNil 
    Real -> injClosedValToVal pmzero 
    Prod u v -> VPair u v (makeZeroVal u) (makeZeroVal v)

-- making sums requires fresh variables so 
-- we make it stateful
-- Also one can imagine a huge optimization of this way of doing things, 
-- where we could back this whole thing out so type U is backed up slices of dimension U
-- with a recorded shape parameter that tells it how to bracket the elements in the slice.
-- And then if something is said to have type U, then we insert hooks that pull the term
-- into the slice as it's evaluated.

-- the two definitions can be merged with the hasMap class that identifies data structures that have a map
makeSumTrace :: Monad m => LType -> Trace s a -> Trace s a -> ST (TState a) m (Trace s a)
makeSumTrace typ m n = case typ of 
    Unit -> do 
        x <- freshVar 
        y <- freshVar 
        let inb = TNil
        let lb2 = TLet y Unit n inb 
        let lb1 = TLet x Unit m lb2
        return lb1  
    Real -> return $ TSum m n
    Prod u v -> do 
        -- xy : u x v
        xy <- freshVar 
        -- x : u
        x <- freshVar 
        -- y : v
        y <- freshVar
        -- zw : u x v 
        zw <- freshVar 
        -- z : u
        z <- freshVar 
        -- w : v
        w <- freshVar 
        ypw <- makeSumTrace v (TVar y) (TVar w)        
        xpz <- makeSumTrace u (TVar x) (TVar z)
        let lb7 = TPair u v xpz ypw 
        let lb6 = TLet w v (TSnd u v (TVar zw)) lb7
        let lb5 = TLet z u (TFst u v (TVar zw)) lb6 
        let lb4 = TLet zw (Prod u v) n lb5 
        let lb3 = TLet y v (TSnd u v (TVar xy)) lb4 
        let lb2 = TLet x u (TFst u v (TVar xy)) lb3 
        let lb1 = TLet xy (Prod u v) m lb2 
        return lb1

makeSumTraceIState :: Monad m => LType -> Trace s a -> Trace s a -> ST (IS.IState s p a) m (Trace s a)
makeSumTraceIState typ m n = case typ of 
    Unit -> do 
        x <- IS.freshVar 
        y <- IS.freshVar 
        let inb = TNil
        let lb2 = TLet y Unit n inb 
        let lb1 = TLet x Unit m lb2
        return lb1  
    Real -> return $ TSum m n
    Prod u v -> do 
        -- xy : u x v
        xy <- IS.freshVar 
        -- x : u
        x <- IS.freshVar 
        -- y : v
        y <- IS.freshVar
        -- zw : u x v 
        zw <- IS.freshVar 
        -- z : u
        z <- IS.freshVar 
        -- w : v
        w <- IS.freshVar 
        ypw <- makeSumTraceIState v (TVar y) (TVar w)        
        xpz <- makeSumTraceIState u (TVar x) (TVar z)
        let lb7 = TPair u v xpz ypw 
        let lb6 = TLet w v (TSnd u v (TVar zw)) lb7
        let lb5 = TLet z u (TFst u v (TVar zw)) lb6 
        let lb4 = TLet zw (Prod u v) n lb5 
        let lb3 = TLet y v (TSnd u v (TVar xy)) lb4 
        let lb2 = TLet x u (TFst u v (TVar xy)) lb3 
        let lb1 = TLet xy (Prod u v) m lb2 
        return lb1

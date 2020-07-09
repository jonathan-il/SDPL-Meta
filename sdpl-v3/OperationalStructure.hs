module OperationalStructure where 

import SDPLTerms
import Err

import qualified Data.Set as S

-- The invariant we will have is that we will never 
-- create a term with an ROP in it.

-- For collet, in the future, we could compute op^daggers but I don't think it's necessary.  I think we can supply them.  Theoretically, we calculate them
-- But there's nothing wrong with precomputing them here.

{-
ClosedValues are 
    CConst !a 
    | CZero 
    | CNil
    | CPair !(ClosedVal a) !(ClosedVal a)

Sin is only defined on constants and Zero 
Similarly for Cos and Neg.  So we need not consider them on Nil or Pair.

However for Times.  Recall that 0 = (0,0).  Thus, Times is defined on:
  * A pair with both elements constant 
  * A pair with one constant and the other zero 
  * The term 0. 
It is not defined on individual constants, nor nil.
-}
eval :: (Floating a,Ord a) => Sigma -> ClosedVal a -> Err (ClosedVal a)
eval f t = case (f,t) of 
    (Sin,CConst r) -> Ok $ CConst (sin r)
    (Sin,CZero) -> Ok $ CConst 0
    (Cos,CConst r) -> Ok $ CConst (cos r)
    (Cos,CZero) -> Ok $ CConst  (cos 0)
    (Neg,CConst r) -> Ok $ CConst (-r)
    (Neg,CZero) -> Ok $ CConst 0
    (Times,CPair (CConst r1) (CConst r2)) -> Ok $ CConst (r1*r2)
    -- Note the following cases also cover CPair Zero Zero
    (Times,CPair _ CZero) -> Ok $ CConst 0
    (Times,CPair CZero _) -> Ok $ CConst 0 
    (Times, CZero) -> Ok $ CConst 0
    _ -> Fail $ "Evaluating: " ++ show f ++ " caused an error that should have been caught by type checking"


{-# INLINABLE eval #-}


{-
Less than is not defined on nil or individual constnat
-}
beval :: (Floating a,Ord a) => Pred -> ClosedVal a -> Err BVal
beval f t = case (f,t) of 
    (LessThan,CPair (CConst a) (CConst b)) -> case compare a b of 
        LT -> Ok BTrue 
        EQ -> Fail "comparison is not defined when a == b"
        GT -> Ok BFalse 
    (LessThan,CPair (CConst a) CZero) -> case compare a 0 of 
        LT -> Ok BTrue 
        EQ -> Fail "comparison is not defined when a == b"
        GT -> Ok BFalse 
    (LessThan,CPair CZero (CConst a)) -> case compare 0 a of
        LT -> Ok BTrue 
        EQ -> Fail "comparison is not defined when a == b"
        GT -> Ok BFalse 
    (LessThan,CPair CZero CZero) -> Fail "comparison is not defined when a == b"
    -- here we are using that 0 = (0,0)
    (LessThan,CZero) -> Fail "comparison is not defined when a == b"

    
{-# INLINABLE beval #-}

{-
The idea of opr is that it gives you a trace term, in context name,
corresponding to the reverse derivative of f.  It also reminds you 
of what name you used.
-}
-- opr opn varname = (varname,fR opn varname)
-- {-# INLINABLE opr #-}

{-
Remember the idea of fR is that it gives you a trace term, in context name, 
corresponding to the reverse derivative of f.
-}
-- fR opn name = case opn of  
--     Sin -> 
--         let 
--             x = TFst   (TVar name)
--             y = TSnd   (TVar name)
--             cosx = TOp Cos x 
--         in
--             TOp Times (TPair   cosx y)
--     Cos -> 
--         let 
--             x = TFst   (TVar name)
--             y = TSnd   (TVar name)
--             sinx = TOp Sin x 
--             min1 = TConst  ( (-1))
--             nsinx = TOp Times (TPair   min1 sinx)
--             nsinxy = TOp Times (TPair   nsinx y)
--         in 
--             nsinxy
--     Neg -> 
--         let 
--             x = TFst   (TVar name)
--             y = TSnd   (TVar name)
--             min1 = TConst ((-1))
--             miny = TOp Times (TPair   min1 y)
--         in 
--             miny
--     Times ->
--         let 
--             ab = TFst  (TVar name)
--             r = TSnd  (TVar name)
--             a = TFst  ab 
--             b = TSnd  ab 
--             br = TOp Times (TPair  b r)
--             ar = TOp Times (TPair a r)
--         in 
--             TPair br ar

-- {-# INLINABLE fR #-}

{-
Where fR gives back a name and a formal term.  fRR drops the two args to R[op](a,w) in directly.
-}
-- idea type 
-- fRR :: Sigma -> Term -> Term -> Term
fRR :: (Ord v,Num a) => Sigma -> (Tracevd a v (S.Set v),S.Set v) -> (Tracevd a v (S.Set v),S.Set v) -> Tracevd a v (S.Set v)
fRR opn (pt,freept) (dir,freedir) = case opn of  
    Sin -> 
        let 
            cosa = DTOp Cos (pt,freept)
        in
            DTOp Times (DTPair (cosa,freept) (dir,freedir),S.union freept freedir)
            -- DTOp Times (DTPair (cosa,freept) (dir,freedir))
    Cos -> 
        let 
            x = (pt,freept)
            y = (dir,freedir)
            sinx = (DTOp Sin x,freept)
            min1 = (DTConst  ( (-1)),S.empty)
            nsinx = (DTOp Times (DTPair  min1 sinx,freept),freept)
            nsinxy = DTOp Times (DTPair  nsinx y,S.union freept freedir)
        in 
            nsinxy
    Neg -> 
        let 
            x = (pt,freept)
            y = (dir,freedir)
            min1 = (DTConst ((-1)),S.empty) 
            miny = DTOp Times (DTPair min1 y,freedir)
        in 
            miny
    Times ->
        let 
            ab = (pt,freept)
            r = (dir,freedir)
            freepat = S.union freept freedir
            a = (DTFst  ab,freept)
            b = (DTSnd  ab,freept)
            br = DTOp Times (DTPair  b r,freepat)
            ar = DTOp Times (DTPair a r,freepat)
        in 
            DTPair (br,freepat) (ar,freepat)
            
{-# INLINABLE fRR #-}


-- Stuff dealing with types and material like that has been moved to syntactic structure. 
-- We are using lots of inlining for these simple non-recursive functions. 
-- For example, we inline the getty functions to or lookup name functions 
-- To make execution fast. 
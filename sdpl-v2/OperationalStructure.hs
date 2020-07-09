module OperationalStructure where 

import SDPLTerms
import Err

-- The invariant we will have is that we will never 
-- create a term with an ROP in it.]

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
opr opn varname = (varname,fR opn varname)
{-# INLINABLE opr #-}

{-
Remember the idea of fR is that it gives you a trace term, in context name, 
corresponding to the reverse derivative of f.
-}
fR opn name = case opn of  
    Sin -> 
        let 
            x = TFst   (TVar name)
            y = TSnd   (TVar name)
            cosx = TOp Cos x 
        in
            TOp Times (TPair   cosx y)
    Cos -> 
        let 
            x = TFst   (TVar name)
            y = TSnd   (TVar name)
            sinx = TOp Sin x 
            min1 = TConst  ( (-1))
            nsinx = TOp Times (TPair   min1 sinx)
            nsinxy = TOp Times (TPair   nsinx y)
        in 
            nsinxy
    Neg -> 
        let 
            x = TFst   (TVar name)
            y = TSnd   (TVar name)
            min1 = TConst ((-1))
            miny = TOp Times (TPair   min1 y)
        in 
            miny
    Times ->
        let 
            ab = TFst  (TVar name)
            r = TSnd  (TVar name)
            a = TFst  ab 
            b = TSnd  ab 
            br = TOp Times (TPair  b r)
            ar = TOp Times (TPair a r)
        in 
            TPair br ar

{-# INLINABLE fR #-}

{-
Where fR gives back a name and a formal term.  fRR drops the two args to R[op](a,w) in directly.
-}

fRR opn pt dir = case opn of  
    Sin -> 
        let 
            cosa = TOp Cos pt
        in
            TOp Times (TPair   cosa dir)
    Cos -> 
        let 
            x = pt
            y = dir
            sinx = TOp Sin x 
            min1 = TConst  ( (-1))
            nsinx = TOp Times (TPair   min1 sinx)
            nsinxy = TOp Times (TPair   nsinx y)
        in 
            nsinxy
    Neg -> 
        let 
            x = pt
            y = dir
            min1 = TConst ((-1))
            miny = TOp Times (TPair   min1 y)
        in 
            miny
    Times ->
        let 
            ab = pt
            r = dir
            a = TFst  ab 
            b = TSnd  ab 
            br = TOp Times (TPair  b r)
            ar = TOp Times (TPair a r)
        in 
            TPair br ar
            
{-# INLINABLE fRR #-}


-- Stuff dealing with types and material like that has been moved to syntactic structure. 
-- We are using lots of inlining for these simple non-recursive functions. 
-- For example, we inline the getty functions to or lookup name functions 
-- To make execution fast. 
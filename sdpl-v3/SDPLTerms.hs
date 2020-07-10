module SDPLTerms where

-- in this variant, we will always have 
-- ROP, however, in this variant, we will 
-- only be able to form terms from the input
-- with Orig Sigma symbols.  We are also baking Sigma 
-- in from the beginning.
-- Operational structure and syntactic structure have become modules.
-- To change or extend this language without adding parser details for 
-- new constructs: Change the Sigma and Pred definitions here 
-- and change the OperationalStructure and InstanceStructure modules.

import Data.Monoid 
import Err 

import qualified Data.Map as M 
import qualified Data.Set as S

data LType a = Unit | Real | TyVar a | Prod (LType a) (LType a) deriving Eq  

-- show is for testing purposes 
instance Show a => Show (LType a) where 
    show Unit = "1"
    show Real = "R"
    show (TyVar a) = show a
    show (Prod u v) = "( " ++  show u ++ "," ++  show v ++ " )"

instance Functor LType where 
    fmap f t = case t of 
        Unit -> Unit 
        Real -> Real 
        TyVar a -> TyVar (f a)
        Prod t1 t2 -> Prod (fmap f t1) (fmap f t2)


-- injection point
data Sigma = Sin | Cos | Times | Neg

-- The invariant of this new implementation is that we never 
-- create R f.  We just simply, during symbolic differentiation, 
-- when we hit an op(m) do a call of fr(op) to get a trace term, 
-- and then continue symbolically differentiating this trace term. 
-- data ROP a = Orig a | R (ROP a)

-- type RSigma = ROP Sigma

-- for testing
instance Show Sigma where 
    show Sin = "sin"
    show Cos = "cos"
    show Times = "times"
    show Neg = "-1"

data Pred = LessThan

-- for testing 
instance Show Pred where 
    show LessThan = "lessthan"

-- the following may wish to be relaxed later
-- actually, why are we storing the name of the function in the closure.  We have it as part of the map.
type Prog a  = M.Map String (FuncClosure a)
type FuncClosure a  = (String, String -> Raw a)
type ProgI a = ProgGeneric a Int --M.Map String (FuncIClosure a)
type ProgGeneric a v = M.Map String (FuncGenericClosure a v)
type ProgDirGeneric a v = M.Map String (FuncDirGenericClosure a v)
type ProgDirI a = M.Map String (FuncDirIClosure a)
-- This is function bodies with an int variable abstracted out.
type FuncIClosure a = FuncGenericClosure a Int -- Int -> RawI a
type FuncGenericClosure a v = v -> Rawv a v
type FuncDirGenericClosure a v = v -> RawvDir a v
type FuncDirIClosure a = Int -> RawDir a
-- Ah!  There is a place where the unique bound variables assumption 
-- could speed things up.  Anytime there is a call to 
-- substitution made we could replace with unsafesub.  
-- And this could improve performance quite a bit in the worst case.

-- I do think there could be merit in using Rawv still.
-- I could see cases where we want to change variable names to ints 
-- for a more compact representation and faster equality matching, 
-- and also where we would potentially want to map bound variable 
-- renamings (required for certain operational details) back to the 
-- their original, say, name and possibly even line number-column number.

-- All types are inferrable 
-- We remove the assumption that + and 0 are only defined on 
-- base type.  However! there is a little annoying issue. 
-- We need to regard Const 0 and 0 as the same thing.
-- Const a could potentially get a 0 put in it.  For example,
-- by adding -3.1 to 3.1.  This is I hope the only weird thing in the 
-- language.

-- These terms allow for a (very) naive directory string approach.
-- In reality we would want to use a more sophisticated approach to 
-- tracking free variables.  I am happy though, in a reference implementation,
-- make the tradeoff of space for speed, and see if the zero fast trick 
-- really does work.  We will be non-strict here in this implementation, and then 
-- later we can add strictness back in.  We will also keep the old terms and 
-- interpreter around, so that we can compare with doing things like computing the free variables.
-- It seems like it could be potentially even better to keep track of where free variables 
-- came from.   4 
type RawDir a = RawvDir a Int
type RawvDir a v = Rawvd a v (S.Set v)
data Rawvd a v d = 
    DVar (v ,d) 
    | DConst a 
    | DZero 
    | DSum (Rawvd a v d,d) (Rawvd a v d,d) -- we only keep track where we use, there is a better data structure we can use for this purpose but this is for testing.  We're effectively messing up our space performance.  But using the reverse derivative anyways, so who cares.
    | DOp Sigma (Rawvd a v d,d)
    | DLet v (Rawvd a v d,d) (Rawvd a v d,d)
    | DNil 
    | DPair (Rawvd a v d,d) (Rawvd a v d,d)
    | DFst (Rawvd a v d,d)
    | DSnd (Rawvd a v d,d)
    | DIf (BRawvd a v d) (Rawvd a v d,d) (Rawvd a v d,d)
    | DWhile v (BRawvd a v d) (Rawvd a v d,d)
    | DRD v (Rawvd a v d,d) (Rawvd a v d,d) (Rawvd a v d,d)
    | DCall String (Rawvd a v d,d)

-- For testing purposes 
instance (Show a,Show v,Show d) => Show (Rawvd a v d) where 
    show t = case t of 
        DVar v -> show v 
        DConst a -> show a 
        DZero -> "0" 
        DSum (m,dm) (n,dn) -> "(" ++ show m ++ show dm ++ ") + (" ++ show n ++ show dn ++ ")"
        DOp f (m,dm) -> show f  ++ "(" ++  show m  ++ show dm ++ ")"
        DLet v (m,dm) (n,dn) -> "let" ++ show v ++ " = " ++ show m ++ show dm ++ " in " ++ show n ++ show dn 
        DNil -> "*" 
        DPair (m,dm) (n,dn) -> "(" ++ show m ++ show dm ++ " , " ++ show n ++ show dn ++ ")"
        DFst (m,dm) -> "fst(" ++ show m ++ show dm ++ ")"
        DSnd (n,dn) -> "snd(" ++ show n ++ show dn ++ ")" 
        DIf b m n -> "if " ++ show b ++ " then " ++ show m ++ " else " ++ show n 
        DWhile x b m -> "while " ++ show x ++ "." ++ show b ++ " do " ++ show m
        DRD x m a v -> "rd(" ++ show x ++ "." ++ show m++")(" ++ show a ++ ")*" ++ show v 
        DCall f m -> f ++ show m

instance (Show a,Show v,Show d) => Show (BRawvd a v d) where 
    show DTrue = "true"
    show DFalse = "false" 
    show (DPred p m) = show p ++"(" ++ show m ++ ")" 



data One = One

type BRawDir a = BRawvd a Int
data BRawvd a v d = 
    DTrue 
    | DFalse 
    | DPred Pred (Rawvd a v d)

type TraceDir a v = Tracevd a v (S.Set v)
data Tracevd a v d = 
    DTVar !v
    | DTConst !a 
    | DTZero 
    | DTSum !(Tracevd a v d,d) !(Tracevd a v d,d)
    | DTOp Sigma !(Tracevd a v d,d)
    | DTLet v !(Tracevd a v d,d) !(Tracevd a v d,d)
    | DTNil 
    | DTPair !(Tracevd a v d,d) !(Tracevd a v d,d)
    | DTFst !(Tracevd a v d,d) 
    | DTSnd !(Tracevd a v d,d) 

instance (Show a,Show v) => Show (Tracevd a v d) where 
    show (DTVar x) = show x 
    show (DTConst a) = show a
    show DTZero = "0"
    show (DTSum (m,_) (n,_)) = show m ++ " + " ++ show n
    show (DTOp op (m,_)) = show op ++ "(" ++ show m ++ ")"
    show (DTLet x (a,_) (m,_)) = "let " ++ show x ++ "=" ++ show a ++ " in " ++ show m 
    show DTNil = "()"
    show (DTPair (m,_) (n,_)) = "(" ++ show m ++ "," ++ show n ++ ")"
    show (DTFst (m,_)) = "fst(" ++ show m ++ ")"
    show (DTSnd (m,_)) = "snd(" ++ show m ++ ")"


data Rawv a v = 
    Var v 
    | Const a 
    | Zero 
    | (Rawv a v) :+ (Rawv a v)
    | Op Sigma (Rawv a v)
    | Let v (Rawv a v) (Rawv  a v) 
    | Nil 
    | Pair (Rawv a v)  (Rawv a v) 
    | Fst (Rawv a v)
    | Snd (Rawv a v)
    | If (BRawv a v) (Rawv a v) (Rawv a v)
    | While v (BRawv a v) (Rawv a v)
    | RD v (Rawv a v) (Rawv a v) (Rawv a v)
    | Call String (Rawv a v)


-- For testing purposes
instance (Show a,Show v) => Show (Rawv a v) where
    show (Var v) = "v" ++ show v 
    show (Const c) = show c
    show Zero = "0"
    show (m :+ n) = "( " ++ show m ++ " + " ++ show n ++ " )"
    show (Op f arg) = show f ++ "( " ++ show arg ++ " )"
    show (Let x m n) = "Let " ++  "v" ++ show x ++ " = " ++ show m ++ " in " ++ show n 
    show Nil = "*"
    show (Pair  a b) = "( " ++ show a ++ " , " ++ show b ++ " )"
    show (Fst  a) = "fst( " ++ show a ++ " )"
    show (Snd  a) = "snd( " ++ show a ++ " )"
    show (If b m n) = "If " ++ show b ++ " then " ++ show m ++ " else " ++ show n 
    show (While x  b m) = "While " ++ "v" ++ show x ++ show b ++ " do " ++ show m
    show (RD x  m a v) = "rd(" ++ "v" ++ show x ++ "." ++ show m ++ " )( " ++ show a ++ " )* " ++ show v 
    show (Call f arg) = show f ++ "( " ++ show arg ++ " )"


instance (Show a,Show v) => Show (BRawv a v) where
    show RTrue = "true"
    show RFalse = "false"
    show (P p arg) = show p ++ "( " ++ show arg ++ " )"



data BRawv a v =
    RTrue 
    | RFalse 
    | P Pred (Rawv a v)

type Raw a = Rawv a String 
type RawI a = Rawv a Int 
type BRaw a = BRawv a String 
type BRawI a = BRawv a Int 


    -- Are you sure you want these as strict fields.  
    -- If you end up applying fst, then you're over-evaluating because the second term doesn't need to 
    -- be evaluated.  I think this is over-evaluating at this level. 
    -- We need to profile this and see what works better.  Ahh, right this is the strict evaluation 
    -- version of this language without the restriction optimizations.
    -- Are you sure you want any of these as strict fields. 
    -- Even constants could end up thrown away.  
data Tracev a v = 
    TVar !v
    | TConst !a 
    | TZero 
    | TSum !(Tracev a v) !(Tracev a v)
    | TOp Sigma !(Tracev a v)
    | TLet v !(Tracev a v) !(Tracev a v)
    | TNil 
    | TPair !(Tracev a v) !(Tracev a v)
    | TFst !(Tracev a v) 
    | TSnd !(Tracev a v) 

type Trace a = Tracev a String
type TraceI a = Tracev a Int

data Valv a v = 
    VVar !v 
    | VConst !a 
    | VZero
    | VNil 
    | VPair !(Valv a v) !(Valv a v)

type Val a = Valv a String
type ValI a = Valv a Int 

data BVal = BTrue | BFalse

data ClosedVal a = 
    CConst !a 
    | CZero 
    | CNil
    | CPair !(ClosedVal a) !(ClosedVal a)

-- For repl purposes we show closed vals. 
instance Show a => Show (ClosedVal a) where 
    show (CConst a) = show a 
    show CZero = "0" -- This is subtle, 0 is distinguished from 0.0.  So if you see just the term 0 in output, you know it's a formal 0. 
    show CNil = "*" 
    show (CPair a b) = "( " ++ show a ++ " , " ++ show b ++ " )"

-- Does sumClosedVals belong in this file? 
-- We define addition of closed values by induction on m.
sumClosedVals :: (Num a) => ClosedVal a -> ClosedVal a -> Err (ClosedVal a)
sumClosedVals m n = case (m,n) of 
    -- if m is Nil, then the other one must be equivalent to Nil.  We return Nil.
    (CNil,_) -> return CNil 
    -- Likewise if the second term is Nil we return Nil.
    (_,CNil) -> return CNil
    -- if m is 0, then the answer is the other thing, regardless of what it is. 
    (CZero,res) -> return res 
    -- likewise if n is 0 
    (res,CZero) -> return res 
    -- if m has the type of a constant then n does too.  Thus neither can be a pair or nil  Now we 
    -- have already covered the cases where one of the items is zero, 
    -- so the only thing left to cover is that they are both constants
    (CConst a,CConst b) -> return $ CConst $ a + b 
    -- if m has the type of a pair then so must n, and neither can have the type of a nil or a const.
    -- We have also already covered the case where one of the terms is zero. Thus we can 
    -- assume they are both proper pairs. 
    (CPair x y,CPair z w) -> do 
        xpz <- sumClosedVals x z 
        ypw <- sumClosedVals y w 
        return $ CPair xpz ypw
    _ -> Fail $ "Bug: typechecking should have caught that all cases of term addition are well typed"
    -- anything else is a wrong answer



{-
Unboxing strict fields should make these injections 
really fast.  
-}

injClosedValToVal v = case v of 
    CConst a -> VConst a 
    CZero -> VZero 
    CNil -> VNil 
    CPair m n -> VPair (injClosedValToVal m) (injClosedValToVal n)

injValToTrace v = case v of 
    VVar x -> TVar x 
    VConst a -> TConst a
    VZero -> TZero 
    VNil -> TNil 
    VPair m n -> TPair (injValToTrace m) (injValToTrace n)

injValToTraceD :: (Ord v) => Valv a v -> Tracevd a v (S.Set v)
injValToTraceD = fst . injValToTraceDFree 

injValToTraceDFree trem = case trem of 
    VVar x -> (DTVar x,S.singleton x)
    VConst a -> (DTConst a,S.empty)
    VZero -> (DTZero ,S.empty)
    VNil -> (DTNil ,S.empty) 
    VPair m n -> let (m'@(_,freem),n'@(_,freen)) = (injValToTraceDFree m,injValToTraceDFree n) in (DTPair m' n',S.union freem freen)


injClosedValToTrace v = case v of 
    CConst a -> TConst a 
    CZero -> TZero 
    CNil -> TNil 
    CPair m n -> TPair (injClosedValToTrace m) (injClosedValToTrace n)




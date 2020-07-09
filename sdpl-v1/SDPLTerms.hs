module SDPLTerms where

import Data.Monoid
import Err

import qualified Data.Map as M


data LType = Unit | Real | Prod LType LType deriving Eq

-- this instance is for testing purposes 
instance Show LType where 
    show Unit = "1"
    show Real = "R" 
    show (Prod u v) = show u ++ " x " ++ show v
 
 -- (f,x,xty,outty,body)
-- type Func s p a = (String,String,LType,LType,Raw s p a)
-- In order to operate efficiently and without having to do bound variable renaming in the symbolic evaluation step
-- We formalize the notion of a function closure.  Rather than specifying a variable name which is assumed to 
-- be completely fresh, instead we assume an abstraction of this name so that at runtime, we can simply generate 
-- a fresh variable, and apply the abstraction to the freshvariable name. 
type FuncClosure s p a = (String,LType,LType, String -> Raw s p a)


type Prog s p a = M.Map String (FuncClosure s p a)


liftFuncToFuncROP :: (s -> (LType,LType)) -> FuncClosure s p a -> FuncClosure (ROP s) p a 
liftFuncToFuncROP gettype (name,inputty,outputty,body) = (name,inputty,outputty,\formalArg -> injRawToRawR gettype (body formalArg))

liftProgToProgROP :: (s -> (LType,LType)) -> Prog s p a -> Prog (ROP s) p a 
liftProgToProgROP gettype = M.map (liftFuncToFuncROP gettype) 


type Raw s p a = Rawv s p a String 

data Rawv s p a v
    = Var v
    | Const a 
    | (Rawv s p a v) :+ (Rawv s p a v)
    -- | Invariant our parser is not allowed to generate ROPs, this 
    -- should only ever exist internally, and should only be produced 
    -- by the abstract reverse differentiation function.
    | Op s (Rawv s p a v)
    | Let String LType (Rawv s p a v) (Rawv s p a v)
    | Nil
    | Pair LType LType (Rawv s p a v) (Rawv s p a v)
    | Fst LType LType (Rawv s p a v)
    | Snd LType LType (Rawv s p a v)
    | If (BRawv s p a v) (Rawv s p a v) (Rawv s p a v)
    -- In while x b m --> Note that the x can be inferred by static analysis.  By the typing 
    -- rules, a while loop can only be formed in a single variable context, but then of course 
    -- that context can be weakened.  It can be re-derived by a very strict type inference process, 
    -- considering that runnable programs must ultimate derive from the empty context at the start.
    -- In the future I think it would make sense to allow a tuple of variables.  But since this a 
    -- functional language we have to form a sort of closure around the body of the loop.
    | While String LType (BRawv s p a v) (Rawv s p a v)
    | RD String LType LType (Rawv s p a v) (Rawv s p a v) (Rawv s p a v)
    | Call String (Rawv s p a v)

instance (Show s,Show p,Show a,Show v) => Show (Rawv s p a v) where
    show (Var v) = show v 
    show (Const c) = show c
    show (m :+ n) = "( " ++ show m ++ " + " ++ show n ++ " )"
    show (Op f arg) = show f ++ "( " ++ show arg ++ " )"
    show (Let x t m n) = "Let " ++  x ++ " = " ++ show m ++ " in " ++ show n 
    show Nil = "*"
    show (Pair t1 t2 a b) = "( " ++ show a ++ " , " ++ show b ++ " )"
    show (Fst t1 t2 a) = "fst( " ++ show a ++ " )"
    show (Snd t1 t2 a) = "snd( " ++ show a ++ " )"
    show (If b m n) = "If " ++ show b ++ " then " ++ show m ++ " else " ++ show n 
    show (While x t b m) = "While "  ++ show b ++ " do " ++ show m
    show (RD x t1 t2 m a v) = "rd(" ++ x ++ "." ++ show m ++ " )( " ++ show a ++ " )* " ++ show v 
    show (Call f arg) = f ++ "( " ++ show arg ++ " )"





type BRaw s p a = BRawv s p a String
data BRawv s p a v
    = Pred p (Rawv s p a v)
    | RTrue
    | RFalse

instance (Show s,Show p,Show a,Show v) => Show (BRawv s p a v) where
    show RTrue = "true"
    show RFalse = "false"
    show (Pred p arg) = show p ++ "( " ++ show arg ++ " )"



-- Note: Trace terms are sometimes called "tape" terms.
data Trace s a 
    = TVar !String 
    | TConst !a 
    | TSum !(Trace s a) !(Trace s a)
    -- in a second round, I would annotate this so that Op nodes carry type information around, and see if I can simplify the whole thing...  
    | TOp !s !(Trace s a)
    | TLet String !LType !(Trace s a) !(Trace s a)
    | TNil
    | TPair !LType !LType !(Trace s a) !(Trace s a)
    | TFst !LType !LType !(Trace s a)
    | TSnd !LType !LType !(Trace s a)

-- unsafeSubTrace a t b == substitute a for t in b, ignoring bound variables
-- In general, in a let expression TLet r m n we should not have r in m.  This would be a variable capture if that were allowed to happen. 
-- Similarly for differential and while terms.  In general this operation should only be used when a is free of all the bound variables in b.  
-- If a has all freshvariables, or is itself a fresh variable, then this is fine to use.
unsafeSubTrace :: Trace s a -> String -> Trace s a -> Trace s a 
unsafeSubTrace a t b = case b of 
    TVar z -> if z == t then a else TVar z 
    m@(TConst m') -> m
    (TSum m n) -> TSum (unsafeSubTrace a t m) (unsafeSubTrace a t n)
    (TOp f arg) -> TOp f (unsafeSubTrace a t arg)
    (TLet r rty m n) -> TLet r rty (unsafeSubTrace a t m) (unsafeSubTrace a t n)
    TNil -> TNil 
    TPair ty1 ty2 m n -> TPair ty1 ty2 (unsafeSubTrace a t m) (unsafeSubTrace a t n)
    TFst ty1 ty2 m -> TFst ty1 ty2 (unsafeSubTrace a t m)
    TSnd ty1 ty2 m -> TSnd ty1 ty2 (unsafeSubTrace a t m)

safeSubTrace = undefined

-- this instance is just for testing purposes 
instance (Show a,Show s) => Show (Trace s a) where 
    show (TVar x) = x
    show (TConst a) = show a 
    show (TSum m n) = "(" ++ show m ++ ")" ++ "+" ++ "(" ++ show n ++ ")"
    show (TOp f m) = show f ++ "( " ++ show m ++ " )"
    show (TLet x ty m n) = "let " ++ show x ++ ":" ++ show ty ++ " = " ++ show m ++ " in " ++ show n 
    show TNil = "*"
    show (TPair u v a b) = "( " ++ show a ++ " , " ++ show b ++ " )"
    show (TFst u v a) = "fst( " ++ show a ++ " )" 
    show (TSnd u v a) = "snd( " ++ show a ++ " )"

data Val a 
    = VVar String
    | VConst a 
    | VNil 
    | VPair LType LType (Val a) (Val a) 

instance Show a => Show (Val a) where 
    show (VVar x) = x 
    show (VConst a) = show a 
    show (VNil) = "*"
    show (VPair t1 t2 a b) = "( " ++ show a ++ " , " ++ show b ++ " )"

data ClosedVal a 
    = CConst !a 
    | CNil 
    | CPair !LType !LType !(ClosedVal a) !(ClosedVal a)

instance Show a => Show (ClosedVal a) where 
    show (CConst a) = show a 
    show CNil = "*"
    show (CPair tya tyb a b) = "(" ++ show a ++ "," ++ show b ++ ")"

-- these definitions and instances should be isolated into their own file.
class PartialSemiGroup a where 
    (<>?) :: a -> a -> Err a 



-- we require a total element of a
class PartialSemiGroup a => PartialMonoid a where
    pmzero :: a

instance Semigroup a => PartialSemiGroup (ClosedVal a) where
    CNil <>? CNil = Ok CNil
    (CConst a) <>? (CConst b) = Ok $ CConst $ a <> b
    -- by typechecking, it is assumed that u,t have the same type and v,w have the same type
    -- actually though, we can't form addition terms except on constants in SDPL.  
    (CPair tyu tyv u v) <>? (CPair tyt tyw t w) = case (u <>? t, v <>? w,tyu == tyt && tyv==tyw) of 
        (Fail msg1,Fail msg2,_) -> Fail $ msg1 ++ " and " ++ msg2 
        (Fail msg1,_,_) -> Fail msg1 
        (_,Fail msg2,_) -> Fail msg2 
        (Ok a,Ok b,True) -> Ok $ CPair tyu tyv a b 
        _ -> Fail "addition of closed values is only defined for matching types"
    _ <>? _ = Fail "addition of closed values is only defined for matching types"

-- in this semigroup, only the base type has a zero. 
instance Monoid a => PartialMonoid (ClosedVal a) where 
    pmzero = CConst mempty 

data BVal = BTrue | BFalse

data ROP a = Orig a LType LType | R (ROP a) LType LType

instance Show a => Show (ROP a) where 
    show (Orig f t1 t2) = show f 
    show (R f t1 t2) = "R[" ++ show f ++ "]"

-- | liftings 
injBValToBRaw b = case b of 
    BTrue -> RTrue 
    BFalse -> RFalse

injClosedValToVal v = case v of 
    CConst a -> VConst a
    CNil -> VNil 
    CPair tya tyb a b -> VPair tya tyb (injClosedValToVal a) (injClosedValToVal b)

injValToTrace v = case v of 
    VVar name -> TVar name 
    VConst a -> TConst a 
    VNil -> TNil 
    VPair tya tyb a b -> TPair tya tyb (injValToTrace a) (injValToTrace b)


injTraceToRaw t = case t of 
    TVar name -> Var name 
    TConst a -> Const a 
    TSum a b -> (injTraceToRaw a) :+ (injTraceToRaw b)
    TOp s m -> Op s (injTraceToRaw m)
    TLet name namety m n -> Let name namety (injTraceToRaw m) (injTraceToRaw n)
    TNil -> Nil
    TPair tya tyb a b -> Pair tya tyb (injTraceToRaw a) (injTraceToRaw b)
    TFst tya tyb a -> Fst tya tyb (injTraceToRaw a)
    TSnd tyb tya a -> Snd tyb tya (injTraceToRaw a)




-- We need to convert raw to rawR once before the program can run.  This can be thought of as a 
-- preprocessing step.
foldraw
  :: (u -> t1)
     -> (t2 -> t1)
     -> (t1 -> t1 -> t1)
     -> (t3 -> t1 -> t1)
     -> (String -> LType -> t1 -> t1 -> t1)
     -> t1
     -> (LType -> LType -> t1 -> t1 -> t1)
     -> (LType -> LType -> t1 -> t1)
     -> (LType -> LType -> t1 -> t1)
     -> (t4 -> t1 -> t1 -> t1)
     -> (String -> LType -> t4 -> t1 -> t1)
     -> (String -> LType -> LType -> t1 -> t1 -> t1 -> t1)
     -> t4
     -> t4
     -> (t5 -> t1 -> t4)
     -> (String -> t1 -> t1)
     -> Rawv t3 t5 t2 u
     -> t1
foldraw v c plus opn l n pair fs sn ifstm whilestm rd tt ff pred callfun t = case t of 
    Var x -> v x 
    Const a -> c a 
    a :+ b -> plus (foldraw v c plus opn l n pair fs sn ifstm whilestm rd tt ff pred callfun a) (foldraw v c plus opn l n pair fs sn ifstm whilestm rd tt ff pred callfun b)
    Op f m -> opn f (foldraw v c plus opn l n pair fs sn ifstm whilestm rd tt ff pred callfun m)
    Let x xty m u -> l x xty (foldraw v c plus opn l n pair fs sn ifstm whilestm rd tt ff pred callfun m) (foldraw v c plus opn l n pair fs sn ifstm whilestm rd tt ff pred callfun u)
    Nil -> n 
    Pair tya tyb a b -> pair tya tyb (foldraw v c plus opn l n pair fs sn ifstm whilestm rd tt ff pred callfun a) (foldraw v c plus opn l n pair fs sn ifstm whilestm rd tt ff pred callfun b)
    Fst tya tyb a -> fs tya tyb (foldraw v c plus opn l n pair fs sn ifstm whilestm rd tt ff pred callfun a)
    Snd tyb tya a -> sn tyb tya (foldraw v c plus opn l n pair fs sn ifstm whilestm rd tt ff pred callfun a)
    If b m u -> ifstm (foldbraw v c plus opn l n pair fs sn ifstm whilestm rd tt ff pred callfun b) (foldraw v c plus opn l n pair fs sn ifstm whilestm rd tt ff pred callfun m) (foldraw v c plus opn l n pair fs sn ifstm whilestm rd tt ff pred callfun u)
    While cont contty b m -> whilestm cont contty (foldbraw v c plus opn l n pair fs sn ifstm whilestm rd tt ff pred callfun b) (foldraw v c plus opn l n pair fs sn ifstm whilestm rd tt ff pred callfun m)
    RD x typ outty m a u -> rd x typ outty (foldraw v c plus opn l n pair fs sn ifstm whilestm rd tt ff pred callfun m) (foldraw v c plus opn l n pair fs sn ifstm whilestm rd tt ff pred callfun a) (foldraw v c plus opn l n pair fs sn ifstm whilestm rd tt ff pred callfun u)
    Call name body -> callfun name (foldraw v c plus opn l n pair fs sn ifstm whilestm rd tt ff pred callfun body )

foldbraw v c plus opn l n pair fs sn ifstm whilestm rd tt ff pred callfun b = case b of 
    RTrue -> tt 
    RFalse -> ff 
    Pred p m -> pred p (foldraw v c plus opn l n pair fs sn ifstm whilestm rd tt ff pred callfun m)

injRawToRawR ::  (s -> (LType,LType)) -> Raw s p a -> Raw (ROP s) p a
injRawToRawR getty = 
    foldraw Var Const (:+) (\f m -> let (u,v) = getty f in  Op (Orig f u v) m ) Let Nil Pair Fst Snd If While RD RTrue RFalse Pred Call



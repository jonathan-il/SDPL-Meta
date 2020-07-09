{-
The future:

Redo the evaluations with a simplified term structure that requires no injections.

Patterns and multiargument functions.  We still allow functions like this, but where everything is super strict
but we will then move to being less strict and annoying.  

Allowing looping on tuples.  Work out what while loops in simple slices need to look like and what requirements we want to hold of them.

Efficiency improvements based on differentiating and free variable conditions.  

Efficiency improvements based on restriction theories. 

Efficiency improvements for differentiating let statements that satisfy a simple condition.  This one is an exponential speedup.

Efficiency improvements for the nested lets.

Single term data type.

Machine semantics with ev(R(f),m) baked in efficiently.

Mutable versus immutable variables.

Need to underscore replace all unused variables

Remove the show instances and remove the show dependencies in the functions in a non-testing 
version.  Maybe use a dual type declaration to switch back and forth easily.


I also believe that if we perform type inference in linear contexts, we can 
  perform mondo performance enhancements.  
Force RD.6 in the operational semantics directly.  This gives another 
optimization.  RD.7 isn't really the sort of thing that can be 
forced in the operational semantics since it's a balanced linear equation.
Actually, there is a way to do this.  
  Every term in this language is equal to a tower of derivatives 
  that can be represented by a sort of bag structure.
  d^n f/d(x1...xn)(a)*(v1...v) could be instead represented by a symmetric data structure.
  like we did a long time ago for the rewriting system for differential terms. 
  It's something like d(f,a) | with a bag that links x_i to v_i.  This might even just 
  be applying the Faa di Bruno coalgebra structure now that I think of it.
-}

module SDPLInterpreter where 



import SDPLTerms
import ST 
import Err
import OperationalStructure hiding (getVar,setVar,freshVar,getLocals,setLocals,TState (..))
import qualified Data.Map as M 
import SymbolicDifferentiation
import InterpreterState
import NotationalSums

import Control.Monad.Trans
import Control.Monad
import Data.Monoid






{-
So we have basic evaluation.
We then need to define 
    * symbolic eval.  This is performed over ROP s.  We extend from an operational structure.  Called abstev here.
    * eval.  This extends ev from the operational structure.  eval closes this up extending this to arbitrary ROps function symbols. 
    * symbolic differentiation. 
    * full evaluation.   This fully evaluates a raw term.
    * full symbolic evaluation.  This fully symbolically evaluates a raw term to a trace term. 


    * We also need a way to create a fresh variable.  Probably, in the future, we can keep records of things like variable names by scope.  
    * We also need an environment of variables mapped onto closed values.
-}

-- good old fashioned C-style derefernce operator, because it's 2 am and ADTs are just structs
(~>) :: a -> (a -> b) -> b 
x ~> f = f x

-- ****************************
-- Interpreter stuff
-- ****************************

-- fullEvaluationTermInProgStrict :: Monoid a => OperationalStructure s p a -> String -> Raw s p a -> Prog s p a -> Err (ClosedVal a)
fullEvaluationTermInProgStrict :: (Show s,Show p, Show a,Monoid a) => OperationalStructure s p a -> String -> Raw s p a -> Prog s p a -> Err (ClosedVal a)
fullEvaluationTermInProgStrict struct freeSeed term prog = runSTVal (fullEvaluation struct term) (IState {locals=M.empty,freshVarSeed=freeSeed,freshCounter=0,stackOfLocals =[],funMap=prog})


-- We require that a runnable program term have no free variables
-- fullEvaluationStrict :: Monoid a => OperationalStructure s p a -> String -> Raw s p a -> Err (ClosedVal a)
fullEvaluationStrict :: (Show s,Show p,Show a,Monoid a) => OperationalStructure s p a -> String -> Raw s p a -> Err (ClosedVal a)
fullEvaluationStrict struct freeSeed term = runSTVal (fullEvaluation struct term) (IState {locals=M.empty,freshVarSeed=freeSeed,freshCounter=0,stackOfLocals = [],funMap=M.empty})

-- fullBoolEvaluation :: Monoid a => OperationalStructure s p a -> BRaw s p a -> ST (IState s p a) Err BVal
fullBoolEvaluation :: (Show s,Show p, Show a,Monoid a) => OperationalStructure s p a -> BRaw s p a -> ST (IState s p a) Err BVal
fullBoolEvaluation struct term = case term of 
  RTrue -> return BTrue 
  RFalse -> return BFalse
  Pred p m -> do 
    m' <- fullEvaluation struct m
    lift $ (struct ~> bev) p m'

-- fullEvaluation :: Monoid a => OperationalStructure s p a -> Raw s p a -> ST (IState s p a) Err (ClosedVal a)
fullEvaluation :: (Show s,Show p,Show a,Monoid a) => OperationalStructure s p a -> Raw s p a -> ST (IState s p a) Err (ClosedVal a)
fullEvaluation struct term = case term of 
  Var x -> getVar x
  Const a -> return $ CConst a 
  m :+ n -> do 
    m' <- fullEvaluation struct m 
    n' <- fullEvaluation struct n
    lift $ m' <>? n'
  Op f m -> do 
    m' <- fullEvaluation struct m 
    -- m' <- trace ("FullEval Operation: " ++ show f ++ " at " ++ "Arg:" ++ show m ) $ fullEvaluation struct m
    lift $ (struct ~> ev) f m'
  Let x _ n m -> do 
    n' <- fullEvaluation struct n 
    locs <- getLocals
    setLocals $ M.insert x n' locs 
    m' <- fullEvaluation struct m
    setLocals locs 
    return m'
  Nil -> return CNil
  Pair tya tyb a b -> do 
    a' <- fullEvaluation struct a 
    b' <- fullEvaluation struct b 
    return $ CPair tya tyb a' b'
  Fst tya tyb a -> do 
    a' <- fullEvaluation struct a 
    case a' of 
      CPair _ _ u v -> return u 
      _ -> lift $ Fail "Type error: Fst was applied to an object that did not evaluate to a pair"
  Snd tyb tya a -> do 
    a' <- fullEvaluation struct a 
    case a' of 
      CPair _ _ u v -> return v 
      _ -> lift $ Fail "Type error: Snd was applied to an object that did not evaluate to a pair"
  If b m n -> do 
    b' <- fullBoolEvaluation struct b
    case b' of 
      BTrue -> fullEvaluation struct m 
      BFalse -> fullEvaluation struct n
  wbm@(While cont contty b m) -> do 
    b' <- fullBoolEvaluation struct b 
    case b' of 
      BFalse -> getVar cont 
      {-
      We use the standard semantics of while in the environment E:
      E \proves b \Rightarrow False 
      -------------------------------------
      E \proves while b do f \Rightarrow E

      E \proves b \Rightarrow True
      E \proves f ; while b do f \Rightarrow E'
      ------------------------------------------
      E \proves while b do f \Rightarrow E'

      And then by the definition of the sequence operator ; we have 
      E \proves f \Rightarrow E''   E'' \Rightarrow while b do f \Rightarrow E'
      -------------------------------------------------------------------------
      E \proves f ; while b do f \Rightarrow E'

      Thus, putting this all together we first run f, and obtain it's value.  We then 
      run the interpreter again but in this new context. 
      -}
      BTrue -> do 
        -- run the body 
        m' <- fullEvaluation struct m 
        locs <- getLocals 
        -- this is essentially implementing while as a recursive function, by pushing popping items off the stack.  Only difference we're virtually using Haskell's own runtime to give us the stack.
        setLocals $ M.insert cont m' locs 
        -- run the loop in this new context
        retval <- fullEvaluation struct wbm
        -- at this point either we've run for infinity, or we've come back with the result of the loop.
        setLocals locs
        return retval
  rm@(RD x t outty m a v) -> do 
    c <- fullEvaluationSymbolic struct rm 
    fullEvaluationTrace struct c
  -- in sdpl a function has a unique arg!
  -- type Func s p a = (String,String,LType,LType,Raw s p a)
  -- (fname,x,inty,outty,body)
  Call fname arg -> do 
    arg' <- fullEvaluation struct arg 
    -- body :: String -> Raw s p a
    (_,_,_,body) <- getFun fname
    formalArg <- freshVar 
    let bodyAtFormal = body formalArg
    -- push the current variables onto the stack 
    pushLocals 
    -- set the new arg 
    setVar formalArg arg' 
    retVal <- fullEvaluation struct bodyAtFormal
    -- reset the local variables 
    popLocals 
    return retVal


-- fullEvaluationTrace :: Monoid a => OperationalStructure s p a -> Trace s a -> ST (IState s p a) Err (ClosedVal a)
fullEvaluationTrace :: (Show s,Show p,Show a,Monoid a) => OperationalStructure s p a -> Trace s a -> ST (IState s p a) Err (ClosedVal a)
fullEvaluationTrace struct term = case term of 
  TVar x -> getVar x
  TConst a -> return $ CConst a 
  TSum m n -> do 
    m' <- fullEvaluationTrace struct m 
    n' <- fullEvaluationTrace struct n
    lift $ m' <>? n'
  TOp f m -> do 
    m' <- fullEvaluationTrace struct m 
    -- m' <- trace ("FullTraceEval Operation: " ++ show f ++ " at " ++ "Arg:" ++ show m ) $ fullEvaluationTrace struct m
    lift $ (struct ~> ev) f m'
  TLet x _ n m -> do 
    n' <- fullEvaluationTrace struct n 
    locs <- getLocals
    setLocals $ M.insert x n' locs 
    m' <- fullEvaluationTrace struct m
    setLocals locs 
    return m'
  TNil -> return CNil
  TPair tya tyb a b -> do 
    a' <- fullEvaluationTrace struct a 
    b' <- fullEvaluationTrace struct b 
    return $ CPair tya tyb a' b'
  TFst tya tyb a -> do 
    a' <- fullEvaluationTrace struct a 
    case a' of 
      CPair _ _ u v -> return u 
      _ -> lift $ Fail "Type error: Fst was applied to an object that did not evaluate to a pair"
  TSnd tyb tya a -> do 
    a' <- fullEvaluationTrace struct a 
    case a' of 
      CPair _ _ u v -> return v 
      _ -> lift $ Fail "Type error: Snd was applied to an object that did not evaluate to a pair"


-- fullEvaluationSymbolic :: Monoid a => OperationalStructure s p a -> Raw s p a -> ST (IState s p a) Err (Trace s a)
fullEvaluationSymbolic :: (Show s,Show p,Show a,Monoid a) => OperationalStructure s p a -> Raw s p a -> ST (IState s p a) Err (Trace s a)
fullEvaluationSymbolic struct term = case term of 
  Var x -> return $ TVar x
  Const a -> return $ TConst a
  Nil -> return TNil 
  m :+ n -> do 
    m' <- fullEvaluationSymbolic struct m 
    n' <- fullEvaluationSymbolic struct n
    return $ TSum m' n'
  Op f m -> do 
    m' <- fullEvaluationSymbolic struct m 
    return $ TOp f m'
    -- version from slides, paper version used a slightly different variant.
  Let x xty a n -> do     
    a' <- fullEvaluationSymbolic struct a
    a'' <- fullEvaluationTrace struct a'
    locs <- getLocals
    setLocals $ M.insert x a'' locs 
    c <- fullEvaluationSymbolic struct n
    setLocals locs 
    return $ TLet x xty a' c 
  Pair tya tyb a b -> do 
    a' <- fullEvaluationSymbolic struct a 
    b' <- fullEvaluationSymbolic struct b 
    return $ TPair tya tyb a' b' 
  Fst tya tyb a -> do 
    a' <- fullEvaluationSymbolic struct a 
    return $ TFst tya tyb a' 
  Snd tyb tya a -> do 
    a' <- fullEvaluationSymbolic struct a 
    return $ TSnd tyb tya a' 
  If b m n -> do 
    b' <- fullBoolEvaluation struct b 
    case b' of 
      BTrue -> fullEvaluationSymbolic struct m 
      BFalse -> fullEvaluationSymbolic struct n
  wbm@(While cont contty b m) -> do 
    s0 <- freshVar 
    retval <- while2 struct cont contty b m s0 
    return $ TLet s0 contty (TVar cont) retval

  RD x xty outty m a v -> do 
    c <- fullEvaluationSymbolic struct a 
    d <- fullEvaluationSymbolic struct v 
    c_v <- fullEvaluationTrace struct c 
    locs <- getLocals  
    setLocals $ M.insert x c_v locs 
    -- x : xty \proves e : outty
    e <- fullEvaluationSymbolic struct m 
    setLocals locs 
    xbar <- freshVar 
    ybar <- freshVar
    -- traceM ("Symbolic evaluation is about to call symbolic diff on: " ++ x ++ ":" ++ show xty ++ "." ++ show e ++ " at " ++ xbar ++ "." ++ ybar)
    xrexbarybar <- symbolicDiff struct x xty e (VVar xbar) (VVar ybar)
    let retval = TLet xbar xty c $ TLet ybar outty d xrexbarybar
    -- traceM ("In the end, symbolic evaluation returns: " ++ show retval)
    return retval
    -- return $ TLet xbar xty c $ TLet ybar outty d xrexbarybar
  {-
  In Abadi and Plotkin:
  arg ~~> c   c ==> v   body(f) ~~> d in environment with formalarg(f) = v 
  -------------------------------------------------------------------------
     f(arg) ~~> let formalarg(f) = c in d
  -}
  Call name arg -> do 
    c <- fullEvaluationSymbolic struct arg 
    v <- fullEvaluationTrace struct c
    (_,inty,_,body) <- getFun name
    formalArg <- freshVar 
    let bodyAtFormal = body formalArg
    pushLocals  
    setVar formalArg v
    d <- fullEvaluationSymbolic struct bodyAtFormal
    popLocals 
    return $ TLet formalArg inty c d

-- Precondition: sn is absolutely fresh
{-
The derivation of why this is correct is  complicated and I will leave it out of here for now.
-}
while2 struct x xty b f sn = do 
  b' <- fullBoolEvaluation struct b
  case b' of 
    BFalse -> return $ TVar sn
    BTrue -> do 
      hc <- fullEvaluationSymbolic struct f 
      hv <- fullEvaluationTrace struct hc 
      locs <- getLocals 
      setLocals $ M.insert x hv locs 
      snew <- freshVar 
      retval <- while2 struct x xty b f snew 
      -- sub a for t in b
      -- in general you want to avoid unsafe sub, but sn is assumed to be fresh
      -- so there cannot be any captures.
      let hcupdated = unsafeSubTrace (TVar sn) x hc 
      setLocals locs 
      return $ TLet snew xty hcupdated retval


-- symbolicDiff :: (Monoid a,Monad m) => OperationalStructure s p a -> String -> LType -> Trace s a -> Val a -> Val a -> ST (IState s p a) m (Trace s a)
symbolicDiff :: (Show s,Show p,Show a,Monoid a,Monad m) => OperationalStructure s p a -> String -> LType -> Trace s a -> Val a -> Val a -> ST (IState s p a) m (Trace s a)
symbolicDiff struct x typ m a w = 
  case m of 
  -- case trace ("SymDiff: " ++ x ++ "." ++ show m ++ "(" ++show a ++")"  ++ "*" ++ show w) m of
    TVar y -> return $ if x == y then injValToTrace w else injValToTrace $ makeZeroVal typ
    TConst a -> return $ injValToTrace $ makeZeroVal typ 
    -- Recall that by typechecking, only real constants have TSum available. 
    TSum d e -> do 
        wda <- symbolicDiff struct x typ d a w 
        wea <- symbolicDiff struct x typ e a w 
        makeSumTraceIState typ wda wea 
    TOp f d -> do 
        -- x has type typ
        -- form R op
        let (tys,tyu) = (struct ~> opty) f
        y <- freshVar
        xrday <- symbolicDiff struct x typ d a (VVar y)
        -- let wfrd = TOp ((struct ~> rr) f) (TPair tys tyu (injValToTrace a) (injValToTrace w)) -- yea, so oops, we're not going to talk about that.
        let wfrd = TOp ((struct ~> rr) f) (TPair tys tyu d (injValToTrace w))
        return $ TLet x typ (injValToTrace a) $ TLet y tys wfrd xrday
    TLet y s d e -> do 
        -- ybar has type s
        -- y has type s
        -- x has type typ
        -- only x is free in d
        -- x,y are both free in e.  We're differentiating with respect to x and with respect to the change caused by the y variable that d was in
        ybar <- freshVar 
        -- form w.R(x.e)(a)
        wrxea <- symbolicDiff struct x typ e a w 
        -- form w.R(y.e)(y) 
        wryey <- symbolicDiff struct y s e (VVar y) w
        -- form ybar.R(x.d)(a) 
        ybarrxda <- symbolicDiff struct x typ d a (VVar ybar)
        -- form let ybar:S = w.R(y.e)(y) in ybar.R(x.d)(a) 
        let letyrr = TLet ybar s wryey ybarrxda
        -- form the term wrxea +_typ letyrr 
        suminres <- makeSumTraceIState typ wrxea letyrr
        return $ TLet x typ (injValToTrace a) $ TLet y s d suminres
    TNil -> return $ injValToTrace $ makeZeroVal typ 
    -- R<f,g> = (1\x \pi_0)R[f] + (1\x \pi_1)R[g]
    -- remember we do let z = m, x = fst(z),y=snd(z) in d 
    -- instead of let x = fst(m),y=snd(m) for efficiency reasons
    -- the latter computes m twice.  I.e. we are forcing a bit of sharing.
    TPair tyu tys d e  -> do 
        yz <- freshVar  -- yz : tyu \x tys 
        y <- freshVar -- y : tyu 
        z <- freshVar -- z : tys 
        --form (1\x \pi_0)R[d]
        yrxda <- symbolicDiff struct x typ  d a (VVar y)
        -- form (1\x \pi_1)R[e]
        zrxea <- symbolicDiff struct x typ e a (VVar z)
        -- form their sum 
        theirsum <- makeSumTraceIState typ yrxda zrxea
        -- form the term 
        -- -- let yz = w, y=fst(yz),z=snd(yz) in yrxda + zrxea
        -- let retval = TLet yz (Prod tyu tys) (injValToTrace w) $ TLet y tyu (TFst tyu tys (TVar yz)) $ TLet z tys (TSnd tyu tys (TVar yz)) theirsum
        -- return $ trace ("SymDiff-ProdCase returns: " ++ show retval) retval
        return $ TLet yz (Prod tyu tys) (injValToTrace w) $ TLet y tyu (TFst tyu tys (TVar yz)) $ TLet z tys (TSnd tyu tys (TVar yz)) theirsum
    -- R[f \pi_0] = (1\x \iota_0)R[f]
    TFst tyu tys d -> do 
        -- form pair (w,0)
        let zero_s = makeZeroVal tys 
        y <- freshVar 
        -- form (1\x \iota_0)R[d]
        wzerorxda <- symbolicDiff struct x typ d a (VPair tyu tys w zero_s)
        -- return let x:T =a,y:UxS = d in wzerorxda
        return $ TLet x typ (injValToTrace a) $ TLet y (Prod tyu tys) d wzerorxda
    TSnd tyu tys d -> do 
        -- form pair (0,w)
        let zero_u = makeZeroVal tyu 
        y <- freshVar 
        zerowrxda <- symbolicDiff struct x typ d a (VPair tyu tys zero_u w)
        return $ TLet x typ (injValToTrace a) $ TLet y (Prod tyu tys) d zerowrxda
        
  


egLetTest1 = Op (Orig Times (Prod Real Real) Real) (Pair Real Real three four)
  where
    three = Let "y" Real (Const (R1 3)) (Var "y")
    four = Let "y" Real (Const (R1 4)) (Var "y")
-- This is (let y = 3 in y) * (let y = 4 in y) -- should evaluate to 3*4=12
getLetTest1Evald = fullEvaluationStrict instanceOperationalStruct "y"  egLetTest1 
egLetTest2 = Let "y" Real (Const (R1 3)) body 
  where
    body = Op (Orig Times (Prod Real Real) Real) (Pair Real Real wyy five)
    wyy = Var "y"
    five = Let "y" Real (Const (R1 5)) (Var "y")
-- This is let y = 3 in  y * (let y = 5 in y) -- should evaluate to 3*5=15
getLetTest2Evald = fullEvaluationStrict instanceOperationalStruct "y"  egLetTest2
egWhile1 = Let "i" Real (Const (R1 0.1)) $ While "i" Real b1 m1 
  where
    b1 = Pred LessThan (Pair Real Real (Var "i") (Const (R1 25)))
    m1 = (Var "i") :+ (Const (R1 5))
-- This is 0.1 + 5 + 5 + 5 + 5 + 5 = 25.1
getWhileTest1Evald = fullEvaluationStrict instanceOperationalStruct "y"  egWhile1
egWhile2 = Let "n" Real (Const (R1 10)) body 
  where
    body = Let "i" Real (Const (R1 0.1)) $ While "i" Real b1 m1
    b1 = Pred LessThan (Pair Real Real (Var "i") (Var "n"))
    m1 = (Var "i") :+ (Const (R1 5))
-- This is 0.1+5+5=10.1
getWhileTest2Evald = fullEvaluationStrict instanceOperationalStruct "y"  egWhile2
egWhile3 = Let "if" (Prod Real Real) (Pair Real Real (Const (R1 0.00001)) (Const (R1 1))) body 
  where 
    body = While "if" (Prod Real Real) b1 m1
    b1 = Pred LessThan (Pair Real Real (Fst Real Real (Var "if")) (Const (R1 5)))
    m1 = Pair Real Real ip1 ftip1 
    ip1 = (Fst Real Real (Var "if")) :+ (Const (R1 1))
    ftip1 = Op (Orig Times (Prod Real Real) Real) (Pair Real Real (Snd Real Real (Var "if")) ip1)
-- This approximates factorial but importantly is undefined on whole numbers.  THis is fac5 which should be close-ish to 120.
getWhile3 = fullEvaluationStrict instanceOperationalStruct "y"  egWhile3
egWhile4 = Let "n" Real (Const (R1 5)) mainbody
  where 
    mainbody = Let "if" (Prod Real Real) (Pair Real Real (Const (R1 0.0001)) (Const (R1 1.001))) body 
    body = While "if" (Prod Real Real) b1 m1
    b1 = Pred LessThan (Pair Real Real (Fst Real Real (Var "if")) (Var "n"))
    m1 = Pair Real Real ip1 ftip1 
    ip1 = (Fst Real Real (Var "if")) :+ (Const (R1 1))
    ftip1 = Op (Orig Times (Prod Real Real) Real) (Pair Real Real (Snd Real Real (Var "if")) ip1)
-- same as getWhile3.  I wonder if it would make sense to have "close to" predicate
getWhile4 = fullEvaluationStrict instanceOperationalStruct "y"  egWhile4
egWhile5 r = Snd Real Real $ Let "n" Real (Const (R1 r)) mainbody
  where 
    mainbody = Let "i" Real (Const (R1 0.0000000001)) $ Let "f" Real (Const (R1 1)) $ Let "if" (Prod Real Real) (Pair Real Real (Var "i") (Var "f")) body 
    body = While "if" (Prod Real Real) b1 m1
    b1 = Pred LessThan (Pair Real Real (Fst Real Real (Var "if")) (Var "n"))
    m1 = Let "i" Real ((Fst Real Real (Var "if")) :+ (Const (R1 1))) m2 
    m2 = Let "f" Real (Op times (Pair Real Real (Snd Real Real (Var "if")) (Var "i"))) m3 
    m3 = Pair Real Real (Var "i") (Var "f")
    times = Orig Times (Prod Real Real) Real 
    -- m1 = Pair Real Real ip1 ftip1 
    -- ip1 = (Fst Real Real (Var "if")) :+ (Const (R1 1))
    -- ftip1 = Op (Orig Times (Prod Real Real) Real) (Pair Real Real (Snd Real Real (Var "if")) ip1)
getWhile5 = fullEvaluationStrict instanceOperationalStruct "y"  (egWhile5 5)
-- Note: This returns fac 170 instantly, in an interpreter.  So it's not sooo slow.
fac :: Double -> Err (ClosedVal R1)
fac r = fullEvaluationStrict instanceOperationalStruct "y"  (egWhile5 r)

-- rd(x.sin(x))(3)*5
egDiff1 = RD "x" Real Real (Op (Orig Sin Real Real) (Var "x")) (Const (R1 3)) (Const (R1 5))
egDiff1Evald = fullEvaluationStrict instanceOperationalStruct "y"  egDiff1

    --   data Raw s p a
--     | RD String LType (Raw s p a) (Raw s p a) (Raw s p a)





{-
Idea here:
We are evaluating abstractly R[R[f]] where f is potentially R[...R[g]...] and g is a basic symbol. 
To do so, when evaluating abstractly R[h] we form a closure of the form ((u,v) \proves R[h](u,v))
and return this.  As long as we have a way to produce trace terms from R[g] where g is a basic symbol, then we're all good.  
This is precisely what opr does: opr is the function that takes a basic symbol g and returns ((u,v) \proves R[g](u,v)).
Once we have this piece then note:
If f is of the form R[h] and we want to abstractly evaluate R[f] then we 
  1. Call abst evaluation on f, yielding the closure (z,R[h](fst(z),snd(z))).  But we only really see (z,m)
  2. We compute a full reverse derivative of R[z.m](u,v) for fresh variables u,v.  That is we symbolically differentiate R[f](u,v).
  3. We close the term back up.  (uv, let u=fst(uv) in let v = snd(uv) in m') where m' = symbolicR[z.m](u,v) 
-}






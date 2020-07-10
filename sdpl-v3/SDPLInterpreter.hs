module SDPLInterpreter where 

{-
To cut down on the widespread use of string operations, we could rename all the variables in the program to being ints.
We already have the capability to do this.  And then our state only needs the freshCounter operation.  And when creating freshvariables, 
we don't have to append to a list.  If we wanted to add in error reporting capability we could obtain the mapping of variable names to 
ints.  Let's think about this.  This would be a small reworking.
-}

import SDPLTerms 
import Err 
import OperationalStructure (fRR,eval,beval)
import InterpreterState
-- are all these imports still used?
import VarsAndSubs (unsafeSubTrace,unsafeSubTraceD,isFreeInDTerm,isFreeInDTrace)

import qualified Data.Map as M
import qualified Data.Set as S

import Control.Monad.Trans 
import Control.Monad 
import qualified Control.Monad.Trans.State.Strict as State 

-- import Debug.Trace


-- ****************************
-- Strict interpreters 
-- ****************************
fullEvaluationTermInProgTotal freeSeed term prog = State.evalStateT (fullEvaluation term) (IState {locals=M.empty,freshCounter=freeSeed,stackOfLocals=[],funMap=prog})

fullEvaluationTermTotal freeSeed term = fullEvaluationTermInProgTotal freeSeed term M.empty


-- *****************************
-- Stateful interpreters 
-- *****************************

fullBoolEvaluation term = case term of 
    DTrue -> return BTrue 
    DFalse -> return BFalse 
    DPred p m -> do 
        m' <- fullEvaluation m
        lift $ beval p m'

-- data Rawvd a v d = 
--     DVar v 
--     | DConst a 
--     | DZero 
--     | DSum (Rawvd a v d,d) (Rawvd a v d,d) 
--     | DOp Sigma (Rawvd a v d,d)
--     | DLet v (Rawvd a v d,d) (Rawvd a v d,d)
--     | DNil 
--     | DPair (Rawvd a v d,d) (Rawvd a v d,d)
--     | DFst (Rawvd a v d,d)
--     | DSnd (Rawvd a v d,d)
--     | DIf (BRawvd a v) (Rawvd a v d,d) (Rawvd a v d,d)
--     | DWhile v (BRawvd a v) (Rawvd a v d,d)
--     | DRD v (Rawvd a v d,d) (Rawvd a v d,d) (Rawvd a v d,d)
--     | DCall String (Rawvd a v d,d)

{-
There is something weird about this approach.  We have that *=0.  Maybe we should remind the user 
that we returned a formal 0 as a value when displaying it.  Then they won't get confused to see 0
when they are also seeing *. 
-}
fullEvaluation term = case term of 
    DVar (x,_) -> getVar x 
    DConst a -> return $ CConst a
    DZero -> return CZero 
    DSum (m,_) (n,_) -> do 
        m' <- fullEvaluation m 
        n' <- fullEvaluation n 
        {-
        So m', n' are values.  We go through the cases by induction on m'
        -}
        lift $ sumClosedVals m' n' 
    DOp f (m,_) -> do 
        m' <- fullEvaluation m 
        lift $ eval f m'
    DLet x (n,_) (m,_) -> do 
        n' <- fullEvaluation n 
        locs <- getLocals 
        setLocals $ M.insert x n' locs 
        m' <- fullEvaluation m 
        setLocals  locs
        return m'
    DNil -> return CNil 
    DPair (a,_) (b,_) -> do 
        a' <- fullEvaluation a 
        b' <- fullEvaluation b 
        return $ CPair a' b'
    DFst (a,_) -> do 
        a' <- fullEvaluation a 
        -- In order to have applied fst, 
        -- a must have had the type of a pair. 
        -- Thus it cannot be a const nor a nil 
        -- Since 0 = (0,0), fst(0) = fst(0,0) = 0
        case a' of 
            CPair u v -> return u 
            CZero -> return CZero
            _ -> lift $ Fail "Type error: Fst was applied to an object that did not evaluate to a pair"
    DSnd (a,_) -> do 
        a' <- fullEvaluation a 
        case a' of 
            CPair u v -> return v 
            CZero -> return CZero 
            _ -> lift $ Fail "Type error: Snd was applied to an object that did not evaluate to a pair"
    DIf b (m,_) (n,_) -> do 
        b' <- fullBoolEvaluation b 
        case b' of 
            BTrue -> fullEvaluation m 
            BFalse -> fullEvaluation n
    wbm@(DWhile cont b (m,_) ) -> do 
        -- traceM "got into the while loop"
        b' <- fullBoolEvaluation b 
        case b' of 
            BFalse -> getVar cont 
            BTrue -> do 
                -- run the body 
                m' <- fullEvaluation m 
                locs <- getLocals 
                setLocals $ M.insert cont m' locs
                retval <- fullEvaluation wbm 
                setLocals locs
                return retval
    rm@(DRD x m a v) -> do 
        c <- fullEvaluationSymbolic rm 
        -- traceM ("differentiating " ++ show m ++ " at " ++ show x)
        -- traceM ("symbolically yielded ")
        fullEvaluationTrace c
    DCall fname (arg,_) -> do 
        arg' <- fullEvaluation arg 
        -- body :: String -> Raw a 
        body <- getFun fname 
        formalArg <- freshVar 
        let bodyAtFormal = body formalArg 
        -- push the current frame onto the stack 
        pushLocals  
        -- set the new arg 
        setVar formalArg arg' 
        retVal <- fullEvaluation bodyAtFormal  
        popLocals 
        return retVal
-- data Tracevd a v d = 
--     DTVar !v
--     | DTConst !a 
--     | DTZero 
--     | DTSum !(Tracevd a v d,d) !(Tracevd a v d,d)
--     | DTOp Sigma !(Tracevd a v d,d)
--     | DTLet v !(Tracevd a v d,d) !(Tracevd a v d,d)
--     | DTNil 
--     | DTPair !(Tracevd a v d,d) !(Tracevd a v d,d)
--     | DTFst !(Tracevd a v d,d) 
--     | DTSnd !(Tracevd a v d,d) 

fullEvaluationTrace term = case term of 
    DTVar x -> getVar x 
    DTConst a -> return $ CConst a 
    DTZero -> return CZero 
    DTSum (m,_) (n,_) -> do 
        m' <- fullEvaluationTrace m 
        n' <- fullEvaluationTrace n 
        lift $ sumClosedVals m'  n' 
    DTOp f (m,_) -> do 
        m' <- fullEvaluationTrace m 
        lift $ eval f m' 
    DTLet x (n,_) (m,_) -> do 
        n' <- fullEvaluationTrace n 
        locs <- getLocals 
        setLocals $ M.insert x n' locs
        m' <- fullEvaluationTrace m 
        setLocals locs
        return m'
    DTNil -> return CNil 
    DTPair (a,_) (b,_) -> do 
        a' <- fullEvaluationTrace a 
        b' <- fullEvaluationTrace b 
        return $ CPair a' b' 
    DTFst (a,_) -> do 
        a' <- fullEvaluationTrace a
        case a' of 
            CPair u v -> return u 
            CZero -> return CZero 
            _ -> lift $ Fail "Type error: TFst was applied to an object that did not evaluate to a pair"
    DTSnd (a,_) -> do 
        a' <- fullEvaluationTrace a 
        case a' of 
            CPair u v -> return v 
            CZero -> return CZero 
            _ -> lift $ Fail "Type error: TSnd was applied to an object that did not evaluate to a pair"



fullEvaluationSymbolic term = case term of 
    DVar (x,_) -> return $ DTVar x 
    DConst a -> return $ DTConst a
    DNil -> return DTNil 
    DZero -> return DTZero 
    DSum (m,freem) (n,freen) -> do 
        m' <- fullEvaluationSymbolic m 
        n' <- fullEvaluationSymbolic n 
        return $ DTSum (m',freem) (n',freen)
    DOp f (m,freem) -> do 
        m' <- fullEvaluationSymbolic m 
        return $ DTOp f (m',freem)
    DLet x (a,freea) (n,freen) -> do 
        a' <- fullEvaluationSymbolic a 
        a'' <- fullEvaluationTrace a' 
        locs <- getLocals 
        setLocals  $ M.insert x a'' locs 
        c <- fullEvaluationSymbolic n 
        setLocals locs 
        return $ DTLet x (a',freea) (c,freen)
    DPair (a,freea) (b,freeb) -> do 
        a' <- fullEvaluationSymbolic a 
        b' <- fullEvaluationSymbolic b 
        return $ DTPair (a',freea) (b',freeb)
    -- This is a place to change the effective free variables, but I think it does anyways.
    -- So that's actually kind of neat.
    DFst (a,_) -> do 
        a' <- fullEvaluationSymbolic a
        case a' of 
            DTPair (u,freeu) v -> return u 
            DTZero -> return DTZero 
            _ -> lift $ Fail "Type error: TFst was applied to an object that did not evaluate to a pair"
    DSnd (a,_) -> do 
        a' <- fullEvaluationSymbolic a 
        case a' of 
            DTPair u (v,freev) -> return v 
            DTZero -> return DTZero 
            _ -> lift $ Fail "Type error: TSnd was applied to an object that did not evaluate to a pair"
    DIf b (m,_) (n,_) -> do 
        b' <- fullBoolEvaluation b 
        case b' of 
            BTrue -> fullEvaluationSymbolic m 
            BFalse -> fullEvaluationSymbolic n 
    wbm@(DWhile cont b m) -> do 
        -- traceM $ "got into the while loop at "  ++ show cont
        s0 <- freshVar 
        retval <- while2 cont b m s0 -- cont is free in while cont b m, and as long as while2 preserves this, we're good.  And it does.  Because cont is uniquely free in m, if anything is free in m.
        -- we also need that the only free variable in while2 cont b m s is s
        return $ DTLet s0 (DTVar cont,S.singleton cont) (retval,S.singleton s0)
    DRD x (m,freem) (a,freea) (v,freev) -> do 
        -- traceM ("differentating " ++ show m ++ " at " ++ show x)
        c <- fullEvaluationSymbolic a -- c has the same free variables a
        d <- fullEvaluationSymbolic v -- d has the same free varialbes as v
        c_v <- fullEvaluationTrace c 
        locs <- getLocals 
        setLocals $ M.insert x c_v locs
        -- x : t \proves e : b 
        e <- fullEvaluationSymbolic m -- e has the same freevariables as m
        -- traceM (show e)
        setLocals locs
        xbar <- freshVar 
        ybar <- freshVar 
        -- a call to symbolicDiff x e a w has freevariables of fv(e)\{x} cup fv(a) \cup fv(w)
        -- traceM ("symbolically differentiating " ++ show e ++ " wrt " ++ show x ++ "at" ++ show c ++ "perturbed by " ++ show d ++ " in free context " ++ show freem)
        xrexbarybar <- symbolicDiff x (e,freem) (VVar xbar,S.singleton xbar) (VVar ybar,S.singleton ybar)
        -- -- hold on to the freevariables of symbexbarybar without the y and then with it 
        let freesymdiffexbarnoy = (freem S.\\ (S.singleton x)) `S.union` (S.singleton xbar)
        let freesymdiffexbarybar = freesymdiffexbarnoy `S.union` (S.singleton ybar)
        -- need to revisit
        let retval = DTLet xbar (c,freea) $ (DTLet ybar (d,freev) (xrexbarybar, freesymdiffexbarybar),freesymdiffexbarnoy) -- ybar is bound in the resulting term y = m in n.  Note by hypothesis/typing we cannot have y in m.
        -- traceM (show retval)
        return retval
        -- undefined
    DCall name (arg,freearg) -> do 
        -- traceM ("calling " ++ name ++ " symbolically")
        c <- fullEvaluationSymbolic arg -- c has the same free variables as arg
        v <- fullEvaluationTrace c 
        body <- getFun name 
        formalArg <- freshVar 
        let bodyAtFormal = body formalArg -- we know by typing that bodyAtFormal has a unique free variable in it, and that is formalArg
        pushLocals 
        setVar formalArg v 
        d <- fullEvaluationSymbolic bodyAtFormal -- d has exactly the freevariables as bodyAtFormal which is formalarg
        popLocals 
        return $ DTLet formalArg (c,freearg) (d,S.singleton formalArg)

-- Precondition: sn is absolutely fresh.
-- My one concern is that we are losing free variables somewhere along the way here.
while2 x b ff@(f,freef) sn = do 
    b' <- fullBoolEvaluation b 
    case b' of 
        BFalse -> return $ DTVar sn -- invariant: the only freevariable in while2 x b f s is s is maintained
        BTrue -> do 
            hc <- fullEvaluationSymbolic f -- the freevariables in hc are exactly those of f which we know by reachability must be at most x
            hv <- fullEvaluationTrace hc 
            locs <- getLocals 
            setLocals $ M.insert x hv locs 
            snew <- freshVar 
            retval <- while2 x b ff snew -- by induction we have the only freevariable in while2 x b f snew is snew
            let hcupdated = unsafeSubTraceD (DTVar sn) x (S.singleton sn)  hc -- by construction the only freevariable in hc is x after substituting, it is only sn 
            setLocals  locs
            return $ DTLet snew (hcupdated,S.singleton sn) (retval,S.singleton snew) -- hcupdated has only freevariable sn and retval by the above has only freevariable snew, and now we have bound it, so the only freevariable is sn as required.


-- *****************************
-- Symbolic differentiation
-- Move to separate module
-- *****************************

-- All the magic is here.
-- Invariant: the free variables in symbolicDiff x m a w = fv(m\{x},a,w)
makeFreeAdjusted x freem freea freew = (S.delete x freem) `S.union` freea `S.union` freew
-- note we are handed to symbolicDiff via RD x m a v ~~> symbolic x m a w (essentially).  Thus we are passing in director strings. 
symbolicDiff x (m,freem) a'@(a,freea) w'@(w,freew) = if (not $! (isFreeInDTrace x m)) then return DTZero else case m of 
        DTVar y -> return $ if x == y then injValToTraceD w else DTZero 
        DTConst a -> return DTZero  
        DTZero -> return DTZero 
        -- -- we don't have to look in both pieces we can short circuit in our search for terms that will become zero. 
        -- -- Remember we will first do it lazy, and then we will add back in the ability to be strict, if strongly desired.
        DTSum d@(_,freed) e@(_,freee) -> do 
            wda <- symbolicDiff x d a' w' -- the free variables in this term 
            wea <- symbolicDiff x e a' w' 
            return $ DTSum (wda,makeFreeAdjusted x freed freea freew) (wea,makeFreeAdjusted x freee freea freew)
    --     {-
    --     Here we are doing R[op(d)]
    --     And we know that should be 
    --     \<pi_0,(d\x 1)R[op]\>R[d] (a,w) 
    --     == R[m](a,    R[op](d(a),w)) 

    --     Thus if we let 
    --         x = a 
    --     Then with x bound in d, anything involving d after letting x = a without binding x 
    --     will be d(a).  

    --     -}
        DTOp f d'@(d,freed) -> do 
            y <- freshVar 
            -- wfrd is going to be R[f](d(a),w) because we are going to bind the x in d to a 
            -- ahead of forming this term.  f is just a symbol.  In neg, we actually have 
            -- reduce free variables potentially, which is fine.  In general 
            -- fRR f a b ~~> R[f](a,b) so the freevariables are fv(a,b)
            let wfrd@(_,wfrdfree) = (fRR f d' (injValToTraceD w,freew),S.union freed freew) -- This is just an "evaluation" 
            -- xrday is R[d](a,y) -- with y completely fresh.
            -- Then to get from this to the desired R[d](a,R[op](d(a),w))
            -- we bind the y to wfrd ahead of time.
            xrday <- symbolicDiff x d' a' (VVar y,S.singleton y)
            let xrdayfree = makeFreeAdjusted x freed freea (S.singleton y)
            let wfrdxrdayfreenoy = S.union wfrdfree (S.delete y xrdayfree)
            return $ DTLet x (injValToTraceD a,freea) $ (DTLet y  wfrd (xrday,xrdayfree),wfrdxrdayfreenoy)
        DTLet y d'@(_,freed) e'@(_,freee) -> do 
            ybar <- freshVar 
            -- form w.R(x.e)(a)
            wrxea <- symbolicDiff x e' a' w' 
            let freexe = makeFreeAdjusted x freee freea freew
            -- form w.R(y.e)(y)
            wryey <- symbolicDiff y e' (VVar y,S.singleton  y) w'
            let freeye = makeFreeAdjusted y freee (S.singleton y) freew 
            -- form ybar.R(x.d)(a) 
            ybarrxda <- symbolicDiff x d' a' (VVar ybar,S.singleton ybar)
            let freexd = makeFreeAdjusted x freed freea (S.singleton ybar)
            -- form let ybar = w.R(y.e)(y) in ybar.R(x.d)(a)
            let letyrr'@(_,letyrrfree) = (DTLet ybar (wryey,freeye) (ybarrxda,freexd),freeye `S.union` (S.delete ybar freexd))
            -- form wrxea + letyrr
            let suminres = DTSum (wrxea,freexe) letyrr'
            let suminresfree = S.union freexe letyrrfree
            return $ DTLet x (injValToTraceD a,freea) $ (DTLet y d' (suminres,suminresfree), freed `S.union` (S.delete y suminresfree))
        DTNil -> return DTZero 
    --     -- R<f,g> = (1\x \pi_0)R[f] + (1\x \pi_1)R[g]
    --     -- Remember to do let z=m, z=fst(z),y=snd(z) instead of x=fst(m),y=snd(m) for efficiency reasons.
        DTPair d'@(_,freed) e'@(_,freee) -> do 
            yz <- freshVar 
            y <- freshVar
            z <- freshVar  
            -- form (1\x \pi_0)R[d]
            yrxda <- symbolicDiff x d' a' (VVar y,S.singleton y)
            let rdfree = makeFreeAdjusted x freed freea (S.singleton y)
            -- form (1\x \pi_1)R[e]
            zrxea <- symbolicDiff x e' a' (VVar z,S.singleton z)
            let refree = makeFreeAdjusted x freee freea (S.singleton z)
            -- form their sum 
            let theirsum = DTSum (yrxda,rdfree) (zrxea,refree)
            let yzfree = S.singleton yz
            let rfree = rdfree `S.union` refree 
            let freenoz = S.delete z rfree 
            let freenoy = S.delete y freenoz 
            -- let yz = w,y=fst(yz),z=snd(yz)in theirsum
            return $ DTLet yz (injValToTraceD w,freew) $ (DTLet y (DTSnd (DTVar yz,yzfree),yzfree) $  (DTLet z (DTSnd (DTVar yz,yzfree),yzfree) (theirsum,rfree),freenoz),freenoy)
        -- R[f\pi_0] = (1\x \iota_0)R[f]
        DTFst d'@(_,freed) -> do 
            y <- freshVar 
            -- form (1\x \iota_0)R[d]
            wzerorxda <- symbolicDiff x d' a' (VPair w VZero,freew)
            let rfreed = makeFreeAdjusted x freed freea freew 
            -- free 
            -- return let x=a, y=d in wzerorxda 
            -- i.e.
            -- (\rs{d(a)} \x \iota_0)R[d]
            -- However: in our semantics this is guaranteed to be what we think it should be, 
            -- So this might not be strictly necessary.  It might help make the connection to the  
            -- classifying category though.  That is we could just return wzerorxda.  y is entirely fresh, 
            -- so we don't need to strictly track it.  Also, note that the free vars of d' and a are being discarded. 
            -- neither x nor y is free in wzerorxda, thus DTLet y d in wzerorxda will always discard everything the d and 
            -- similarly with the let x = a before it.  Thus we do not track their frees here.  We should prove semantically 
            -- that this is sound, but really this is a part of the collet soundness proof too.  But in general, 
            -- we should prove it's sound to skip this altogether.  AND we can skip while maintaining strictness.
            return $ DTLet x (injValToTraceD a,S.empty) $ (DTLet y d' (wzerorxda,rfreed),rfreed)
        DTSnd d'@(_,freed) -> do 
            y <- freshVar 
            zerowrxda <- symbolicDiff x d' a' (VPair VZero w,freew)
            let rfreed = makeFreeAdjusted x freed freea freew 
            return $ DTLet x (injValToTraceD a,S.empty) $ (DTLet y d' (zerowrxda,rfreed),rfreed)




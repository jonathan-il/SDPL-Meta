module SDPLInterpreterOld where 

{-
To cut down on the widespread use of string operations, we could rename all the variables in the program to being ints.
We already have the capability to do this.  And then our state only needs the freshCounter operation.  And when creating freshvariables, 
we don't have to append to a list.  If we wanted to add in error reporting capability we could obtain the mapping of variable names to 
ints.  Let's think about this.  This would be a small reworking.
-}

import SDPLTerms 
import Err 
import OperationalStructureOld (fRR,eval,beval)
import InterpreterStateOld
import VarsAndSubs (unsafeSubTrace,freetrace)

import qualified Data.Map as M
import qualified Data.Set as S

import Control.Monad.Trans 
import Control.Monad 
import qualified Control.Monad.Trans.State.Strict as State 


-- ****************************
-- Strict interpreters 
-- ****************************
fullEvaluationTermInProgTotal freeSeed term prog = State.evalStateT (fullEvaluation term) (IState {locals=M.empty,freshCounter=freeSeed,stackOfLocals=[],funMap=prog})

fullEvaluationTermTotal freeSeed term = fullEvaluationTermInProgTotal freeSeed term M.empty


-- *****************************
-- Stateful interpreters 
-- *****************************

fullBoolEvaluation term = case term of 
    RTrue -> return BTrue 
    RFalse -> return BFalse 
    P p m -> do 
        m' <- fullEvaluation m
        lift $ beval p m'


{-
There is something weird about this approach.  We have that *=0.  Maybe we should remind the user 
that we returned a formal 0 as a value when displaying it.  Then they won't get confused to see 0
when they are also seeing *. 
-}
fullEvaluation term = case term of 
    Var x -> getVar x 
    Const a -> return $ CConst a
    Zero -> return CZero 
    m :+ n -> do 
        m' <- fullEvaluation m 
        n' <- fullEvaluation n 
        {-
        So m', n' are values.  We go through the cases by induction on m'
        -}
        lift $ sumClosedVals m' n' 
    Op f m -> do 
        m' <- fullEvaluation m 
        lift $ eval f m'
    Let x n m -> do 
        n' <- fullEvaluation n 
        locs <- getLocals 
        setLocals $ M.insert x n' locs 
        m' <- fullEvaluation m 
        setLocals  locs
        return m'
    Nil -> return CNil 
    Pair a b -> do 
        a' <- fullEvaluation a 
        b' <- fullEvaluation b 
        return $ CPair a' b'
    Fst a -> do 
        a' <- fullEvaluation a 
        -- In order to have applied fst, 
        -- a must have had the type of a pair. 
        -- Thus it cannot be a const nor a nil 
        -- Since 0 = (0,0), fst(0) = fst(0,0) = 0
        case a' of 
            CPair u v -> return u 
            CZero -> return CZero
            _ -> lift $ Fail "Type error: Fst was applied to an object that did not evaluate to a pair"
    Snd a -> do 
        a' <- fullEvaluation a 
        case a' of 
            CPair u v -> return v 
            CZero -> return CZero 
            _ -> lift $ Fail "Type error: Snd was applied to an object that did not evaluate to a pair"
    If b m n -> do 
        b' <- fullBoolEvaluation b 
        case b' of 
            BTrue -> fullEvaluation m 
            BFalse -> fullEvaluation n
    wbm@(While cont b m ) -> do 
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
    rm@(RD x m a v) -> do 
        c <- fullEvaluationSymbolic rm 
        fullEvaluationTrace c
    Call fname arg -> do 
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


fullEvaluationTrace term = case term of 
    TVar x -> getVar x 
    TConst a -> return $ CConst a 
    TZero -> return CZero 
    TSum m n -> do 
        m' <- fullEvaluationTrace m 
        n' <- fullEvaluationTrace n 
        lift $ sumClosedVals m'  n' 
    TOp f m -> do 
        m' <- fullEvaluationTrace m 
        lift $ eval f m' 
    TLet x n m -> do 
        n' <- fullEvaluationTrace n 
        locs <- getLocals 
        setLocals $ M.insert x n' locs
        m' <- fullEvaluationTrace m 
        setLocals locs
        return m'
    TNil -> return CNil 
    TPair a b -> do 
        a' <- fullEvaluationTrace a 
        b' <- fullEvaluationTrace b 
        return $ CPair a' b' 
    TFst a -> do 
        a' <- fullEvaluationTrace a
        case a' of 
            CPair u v -> return u 
            CZero -> return CZero 
            _ -> lift $ Fail "Type error: TFst was applied to an object that did not evaluate to a pair"
    TSnd a -> do 
        a' <- fullEvaluationTrace a 
        case a' of 
            CPair u v -> return v 
            CZero -> return CZero 
            _ -> lift $ Fail "Type error: TSnd was applied to an object that did not evaluate to a pair"



fullEvaluationSymbolic term = case term of 
    Var x -> return $ TVar x 
    Const a -> return $ TConst a
    Nil -> return TNil 
    Zero -> return TZero 
    m :+ n -> do 
        m' <- fullEvaluationSymbolic m 
        n' <- fullEvaluationSymbolic n 
        return $ TSum m' n'
    Op f m -> do 
        m' <- fullEvaluationSymbolic m 
        return $ TOp f m' 
    Let x a n -> do 
        a' <- fullEvaluationSymbolic a 
        a'' <- fullEvaluationTrace a' 
        locs <- getLocals 
        setLocals  $ M.insert x a'' locs 
        c <- fullEvaluationSymbolic n 
        setLocals locs 
        return $ TLet x a' c
    Pair a b -> do 
        a' <- fullEvaluationSymbolic a 
        b' <- fullEvaluationSymbolic b 
        return $ TPair a' b' 
    Fst a -> do 
        a' <- fullEvaluationSymbolic a
        case a' of 
            TPair u v -> return u 
            TZero -> return TZero 
            _ -> lift $ Fail "Type error: TFst was applied to an object that did not evaluate to a pair"
    Snd a -> do 
        a' <- fullEvaluationSymbolic a 
        case a' of 
            TPair u v -> return v 
            TZero -> return TZero 
            _ -> lift $ Fail "Type error: TSnd was applied to an object that did not evaluate to a pair"
    If b m n -> do 
        b' <- fullBoolEvaluation b 
        case b' of 
            BTrue -> fullEvaluationSymbolic m 
            BFalse -> fullEvaluationSymbolic n 
    wbm@(While cont b m) -> do 
        s0 <- freshVar 
        retval <- while2 cont b m s0 
        return $ TLet s0 (TVar cont) retval 
    RD x m a v -> do 
        c <- fullEvaluationSymbolic a 
        d <- fullEvaluationSymbolic v 
        c_v <- fullEvaluationTrace c 
        locs <- getLocals 
        setLocals $ M.insert x c_v locs
        -- x : t \proves e : b 
        e <- fullEvaluationSymbolic m 
        setLocals locs
        xbar <- freshVar 
        ybar <- freshVar 
        xrexbarybar <- symbolicDiff x e (VVar xbar) (VVar ybar)
        let retval = TLet xbar c $ TLet ybar d xrexbarybar 
        return retval
    Call name arg -> do 
        c <- fullEvaluationSymbolic arg 
        v <- fullEvaluationTrace c 
        body <- getFun name 
        formalArg <- freshVar 
        let bodyAtFormal = body formalArg 
        pushLocals 
        setVar formalArg v 
        d <- fullEvaluationSymbolic bodyAtFormal 
        popLocals 
        return $ TLet formalArg c d

-- Precondition: sn is absolutely fresh.
while2 x b f sn = do 
    b' <- fullBoolEvaluation b 
    case b' of 
        BFalse -> return $ TVar sn 
        BTrue -> do 
            hc <- fullEvaluationSymbolic f 
            hv <- fullEvaluationTrace hc 
            locs <- getLocals 
            setLocals $ M.insert x hv locs 
            snew <- freshVar 
            retval <- while2 x b f snew 
            let hcupdated = unsafeSubTrace (TVar sn) x hc 
            setLocals  locs
            return $ TLet snew hcupdated retval


-- *****************************
-- Symbolic differentiation
-- Move to separate module
-- *****************************

-- All the magic is here.
symbolicDiff x m a w = if not (S.member x (freetrace m)) then return TZero else case m of  
        TVar y -> return $ if x == y then injValToTrace w else TZero 
        TConst a -> return TZero  
        TZero -> return TZero 
        TSum d e -> do 
            wda <- symbolicDiff x d a w 
            wea <- symbolicDiff x e a w 
            return $ TSum wda wea  
        {-
        Here we are doing R[op(d)]
        And we know that should be 
        \<pi_0,(d\x 1)R[op]\>R[d] (a,w) 
        == R[m](a,    R[op](d(a),w)) 

        Thus if we let 
            x = a 
        Then with x bound in d, anything involving d after letting x = a without binding x 
        will be d(a).  

        -}
        TOp f d -> do 
            y <- freshVar 
            -- wfrd is going to be R[f](d(a),w) because we are going to bind the x in d to a 
            -- ahead of forming this term.
            let wfrd = fRR f d (injValToTrace w)
            -- xrday is R[d](a,y) -- with y completely fresh.
            -- Then to get from this to the desired R[d](a,R[op](d(a),w))
            -- we bind the y to wfrd ahead of time.
            xrday <- symbolicDiff x d a (VVar y)
            return $ TLet x (injValToTrace a) $ TLet y  wfrd xrday
        TLet y d e -> do 
            ybar <- freshVar 
            -- form w.R(x.e)(a)
            wrxea <- symbolicDiff x e a w 
            -- form w.R(y.e)(y)
            wryey <- symbolicDiff y e (VVar y) w
            -- form ybar.R(x.d)(a) 
            ybarrxda <- symbolicDiff x d a (VVar ybar)
            -- form let ybar = w.R(y.e)(y) in ybar.R(x.d)(a)
            let letyrr = TLet ybar wryey ybarrxda 
            -- form wrxea + letyrr
            let suminres = TSum wrxea letyrr 
            return $ TLet x (injValToTrace a) $ TLet y d suminres
        TNil -> return TZero 
        -- R<f,g> = (1\x \pi_0)R[f] + (1\x \pi_1)R[g]
        -- Remember to do let z=m, z=fst(z),y=snd(z) instead of x=fst(m),y=snd(m) for efficiency reasons.
        TPair d e -> do 
            yz <- freshVar 
            y <- freshVar
            z <- freshVar  
            -- form (1\x \pi_0)R[d]
            yrxda <- symbolicDiff x d a (VVar y)
            -- form (1\x \pi_1)R[e]
            zrxea <- symbolicDiff x e a (VVar z)
            -- form their sum 
            let theirsum = TSum yrxda zrxea 
            return $ TLet yz (injValToTrace w) $ TLet y (TFst (TVar yz)) $ TLet z (TSnd (TVar yz)) theirsum 
        -- R[f\pi_0] = (1\x \iota_0)R[f]
        TFst d -> do 
            y <- freshVar 
            -- form (1\x \iota_0)R[d]
            wzerorxda <- symbolicDiff x d a (VPair w VZero)
            -- return let x=a, y=d in wzerorxda 
            -- i.e.
            -- (\rs{d(a)} \x \iota_0)R[d]
            -- However: in our semantics this is guaranteed to be what we think it should be, 
            -- So this might not be strictly necessary.  It might help make the connection to the  
            -- classifying category though.
            return $ TLet x (injValToTrace a) $ TLet y d wzerorxda
        TSnd d -> do 
            y <- freshVar 
            zerowrxda <- symbolicDiff x d a (VPair VZero w)
            return $ TLet x (injValToTrace a) $ TLet y d zerowrxda
-- data ClosedVal a = 
--     CConst !a 
--     | CZero 
--     | CNil
--     | CPair !(ClosedVal a) !(ClosedVal a)


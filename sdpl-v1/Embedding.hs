{-
To make a program that runs all nice and good and stuff, import this module, and compile with 
  ghc --make -O2 Main.hs

And then if you're on a linux machine, you'll want to run with:
  ./MyProgram 2> traceLog.txt

At the moment I have a lot of debug stuff turned on.  I'll admit it, at first write, I switched a 'd' to an 'a' somewhere
and they were both in context and they both had the right type, and in many circumstances, they carried the same value!
However, finding the error required a ton of uses of Debug.Trace.  So ... the code is pretty messy ATM.
-}

module Embedding where


import SDPLTerms
import Prelude hiding (fst,snd)
import qualified Data.Map as M
import OperationalStructure 
import Err 
import qualified SDPLInterpreter as Interpreter

import ST -- remove after testing
import qualified InterpreterState as IS -- remove after testing
{-
We play with a lot of datatypes to give us type constructors that make things look more like a program.
For example we will often use 
   thing :> typeof_thing1
But sometimes we will use it for input output relationships too 
  f (inpty :> outty) := ...
So we abstract the general pattern

I was playing around with these, so some of them might not be relevant.
-}

data TypePatternMeta a b = a :> b
type TypePatternP1 = TypePatternMeta String  LType
type TypePatternP2 = TypePatternMeta TypePatternP1 LType
data AssignMeta a b = a := b 
type AssignM a = AssignMeta a (String -> Raw SigmaR1 Pred1 R1)
type FunBody = AssignM TypePatternP2
type FunHeader = TypePatternMeta LType LType
type FuncClosureDef = AssignMeta FunHeader (Raw SigmaR1 Pred1 R1 -> Raw SigmaR1 Pred1 R1)

-- Make a program (or rather a function evaluation context) from a list of function closures
-- In order for our programs to run correctly we require two assumptions of these functional closures. 
-- If we take together all the function names at once, then there are not free function variables, 
-- and any given closure can have no free ordinary variables except the closed variable.
program :: [FuncClosure s p a] -> Prog s p a 
program = foldr (\h@(f,inty,outty,body) map -> M.insert f h map) M.empty

-- This evaluates a term with respect to a list of function closures. 
-- This gives the semantics of 
-- letrec f = ... in letrec g = ... in m 
-- used in Abadi and Plotkin
runTermInProg :: Raw SigmaR1 Pred1 R1 -> Prog (ROP SigmaR1) Pred1 R1 -> Err (ClosedVal R1)
runTermInProg term prog = 
    let 
        termR = injRawToRawR (gettyop instanceOpStruct1) term 
    in 
        -- We make use of a freshvariable seed in our programs, and sense all the variables are sane 
        -- it doesn't matter what we take our initial seed to be.  Might as well name it honour of Zappa.
        Interpreter.fullEvaluationTermInProgStrict instanceOperationalStruct "helpimarock" termR prog



-- ************************************************************************************************
-- Combinators and datatypes for a shallow embedding.  We gave an instance of Monad (Rawv s p a) 
-- so we could, if we really wanted to, clean up the embedding here using the Free monad.
-- ************************************************************************************************




-- Our program terms evaluate in a map of closures.  These are terms with a single unique determined freevariable.
-- To make instantiating this free variable easier at run time, we abstract out this free variable as a function.
-- So rather than writing ("w",Sin (Var "w")) and then at runtime, replacing "w" with a fresh variable, we 
-- carry it as a function (\w -> Sin w) and then at runtime we get a fresh variable y_0 and do (\w -> Sin w) (Var y_0)
-- The general syntax pattern we then use for letrec is 
-- letrec "f" $ (a :> b) := \z -> FUNCTION_BODY
letrec :: String -> FuncClosureDef -> FuncClosure (ROP SigmaR1) Pred1 R1
letrec name ( (inty :> outty) := body) = 
    let
        tymapper = gettyop instanceOpStruct1  
        bodyconverted varname = injRawToRawR tymapper (body (Var varname)) 
    in
        (name,inty,outty,bodyconverted)


call = Op 
callf = Call 
v = Var 
c = Const . R1




testGoal = 
    letrec "f" $ (Real :> Real) :=  \z -> Op Sin z

testGoalRun = 
    let 
        myterm = (Call "f" (Const (R1 5)))
        myprog = program [testGoal]
    in 
        runTermInProg myterm myprog





callGoal = 
    letrec "f" $ (Real :> Real) := \z -> call Sin z

-- but it should be fine to not use the function argument 
callGoal2 = 
    letrec "f" $ (Real :> Real) := \z -> call Sin (Const (R1 3))

-- we should be able to duplicate too
callGoal3 = 
    letrec "f" $ (Real :> Real) := \z -> call Sin z :+ call Sin z :+ (Const (R1 3))

callGoalsRun = 
    let
        myterm = Call "f" (Const (R1 5))
        myprog1 = program [callGoal]
        myprog2 = program [callGoal2]
        myprog3 = program [callGoal3]
    in 
        map (runTermInProg myterm) [myprog1,myprog2,myprog3]




-- sum already has an embeddedish syntax

data LETIN = LetPre :- Raw SigmaR1 Pred1 R1 
type LetPre = AssignMeta TypePatternP1 (Raw SigmaR1 Pred1 R1) 

lett :: LETIN -> Raw SigmaR1 Pred1 R1 
lett (((x:>xty):=m) :- n) = Let x xty m n 

-- callGoal3 = 
--     letrec "f" $ (Real :> Real) := \z -> call Sin z :+ call Sin z :+ (Const (R1 3))
test4 = 
    letrec "f" $ (Real :> Real) := \z -> (
        lett $ ("y":>Real) := (c 4) :- (
            (call Sin z)
            :+
            (v "y")
        )
    )

test4Run = 
    let 
        myterm = Call "f" (c 2)
        myprog = program [test4]
    in
        runTermInProg myterm myprog
nil = Nil

type PairTerm = TypePatternMeta (Raw SigmaR1 Pred1 R1,Raw SigmaR1 Pred1 R1) (LType,LType)
data ProjType =  LType :| LType 

p :: PairTerm -> Raw SigmaR1 Pred1 R1 
-- p (((a,b):>tya):>tyb) = Pair tya tyb a b 
p ((a,b):> (tya , tyb)) = Pair tya tyb a b

test5 = 
    letrec "f" $ (Real :> (Prod Real Real)) := \z -> (
        p $ (call Sin z,call Cos z) :> (Real , Real)
    )
test5Run = runTermInProg (Call "f" (c 2)) (program [test5])

fst :: (LType,LType) -> Raw SigmaR1 Pred1 R1  -> Raw SigmaR1 Pred1 R1 
fst  (tya , tyb) m = Fst tya tyb m

snd :: (LType,LType) -> Raw SigmaR1 Pred1 R1  -> Raw SigmaR1 Pred1 R1 
snd (tya , tyb) m = Snd tya tyb m

-- iff () $ thenn () $ elsee ()
elsee :: Raw SigmaR1 Pred1 R1 -> Raw SigmaR1 Pred1 R1
elsee = id 
thenn :: Raw SigmaR1 Pred1 R1 -> Raw SigmaR1 Pred1 R1 -> (Raw SigmaR1 Pred1 R1,Raw SigmaR1 Pred1 R1)
thenn thenpart elsepart = (thenpart,elsepart)
iff :: BRaw SigmaR1 Pred1 R1 -> (Raw SigmaR1 Pred1 R1,Raw SigmaR1 Pred1 R1) -> Raw SigmaR1 Pred1 R1
iff b (m,n) = If b m n 
while :: (TypePatternMeta String LType) -> BRaw SigmaR1 Pred1 R1 -> Raw SigmaR1 Pred1 R1 -> Raw SigmaR1 Pred1 R1
while (x:>xty) b m = While x xty b m

data LinDot a b = a :* b 

type RDBinding = (TypePatternMeta String LType, TypePatternMeta (Raw SigmaR1 Pred1 R1) LType)

rd :: RDBinding -> LinDot (Raw SigmaR1 Pred1 R1) (Raw SigmaR1 Pred1 R1) -> Raw SigmaR1 Pred1 R1 
rd (x:>tya,m:>tyv) (a :* v) = RD x tya tyv m a v



test6 = 
    letrec "f" $ (Real :>Real) := \z -> (
        fst (Real , Real) $ p $ (call Sin z, call Cos z) :> (Real , Real)
    )
test6Run = runTermInProg (callf "f" (c 2)) (program [test6])

-- Factorial ish definition with a while loop 
test7 = 
    letrec "fac" $ (Real :> Real) := \n -> (
        lett $ "ab" :> (Prod Real Real) := (p $ (c 0.000000001,c 1) :> (Real, Real)) :- 
        let b1 = Pred LessThan (p $ (fst (Real,Real) (v "ab"), n) :> (Real,Real)) in 
        while ("ab":> (Prod Real Real)) b1 (
            let a = fst (Real,Real) (v "ab") in 
            let b = snd (Real,Real) (v "ab") in 
            let ip1 = a :+ (c 1) in 
            let ftip1 = call Times (p $ (b,ip1) :> (Real,Real)) in 
            (p $ (ip1,ftip1) :> (Real,Real))
        )
    )
    
    
test7Run = runTermInProg (callf "fac" (c 4.1)) (program [test7])

makeTest7Concrete = 
    let 
        (a,b,c,d) = test7
        create7FreeN = d "n" 
        bindn = Let "n" Real (Const (R1 4.1)) create7FreeN 
    in 
        bindn

-- One should not write down the term let x = x in x.
anotherOddTest =
    let badid = Let "x" Real (Var "x") (Var "x") in 
    rd ("x":>Real,badid:>Real) $ (c 1) :* (c 5)

runAnOddTest = runTermInProg anotherOddTest M.empty


-- fullEvaluationSymbolic :: (Show s,Show p,Show a,Monoid a) => OperationalStructure s p a -> Raw s p a -> ST (IState s p a) Err (Trace s a)
test7SymbolicRun = runSTVal (Interpreter.fullEvaluationSymbolic instanceOperationalStruct makeTest7Concrete) (IS.IState M.empty M.empty [] "helpimarock" 0)

test8 = 
    letrec "f" $ (Real :> Real) := \x -> (
        let m = x :+ (v "y") in 
        rd ("y":>Real, m :> Real) $ (c 1) :* (c 5)
    )

-- f(x) := d (y. x+y) (1)*5 = d(y.y)(1)*5 = 5
test8Run = runTermInProg (callf "f" (c 3)) (program [test8])




-- Now for a real test!  Because clearly, the factorial function has been begging to be differentiated since the beginning of time (note: a < b is UNDEFINED at a == b)
-- did i really forget to do subtraction...  For now, I'll do it with neg.
testfac =
    letrec "fac" $ (Real :> Real) := \n -> (
        let b = Pred LessThan (p $ (n,c 0) :> (Real, Real)) in 
        let minus1 = call Neg (c 1) in
        let nminus1 = n :+ minus1 in
        let nn1 = call Times (p $ (n,callf "fac"  nminus1) :> (Real,Real)) in 
        iff b $ thenn (c 1) $ elsee nn1
    )

testFacRunn = 
    let 
        -- because a < b is UNDEFINED at a == b, don't give fac "whole" numbers. 
        fac5 = callf "fac" (c 4.9)
        myprog = program [testfac]
    in 
        runTermInProg fac5 myprog

-- because of the limitations of R1 currently just using doubles, the highest we can go on a 64 bit computer is between 170.6 and 170.7
testFacRun n = 
    let 
        -- because a < b is UNDEFINED at a == b, don't give fac "whole" numbers.  As you get closer to a whole number, the program will converge on the correct value
        fac5 = callf "fac" (c n)
        myprog = program [testfac]
    in 
        runTermInProg fac5 myprog
        
testSinFun = 
    letrec "f" $ (Real:>Real) := \x -> (
        call Sin x
    )
testSinRun = 
    let 
        myarg = callf "f" (c 1)
        myprog = program [testSinFun]
    in 
        runTermInProg myarg myprog 

-- this should be cos(1)*3
testDerivativeRun = 
    let 
        myprog = program [testSinFun]
        myarg = rd ("z":>Real, (callf "f" (v "z")) :> Real) $ (c 1) :* (c 3)
        -- myarg = callf "f" (c 5)
    in
        runTermInProg myarg myprog

-- this should be cos(1)*3
testSinDerivativeRun =
    let 
        myarg = RD "x" Real Real (Op Sin (Var "x")) (Const (R1 1)) (Const (R1 3))
        myprog = program []
    in 
        runTermInProg myarg myprog

testWhileFalse = 
    let 
        myarg = while ("x":>Real) RFalse (c 5)
        dmyargx = rd ("x":>Real,myarg:>Real) $ (c 1) :* (c 3)
    in 
        runTermInProg dmyargx M.empty 


-- This is a bit of a litmus.  It tests that we've instantiated whileloops as functions correctly.
-- I believe that the following should evaluate to zero.  Here while "x" . RFalse (c 5) 
-- is the identity function when viewed as a term in context x \proves while x . RFalse (c 5)
-- The x is only really there to remind you of its context, in case you forgot.  

-- I believe this example points to a possible confusion regarding the use of the reverse or forward derivative 
-- as a binding operator.  When you write rd(x.m)(a)*b, you are taking the derivative of m with respect to 
-- a chosen representative of the proof tree, where you've "frozen" the closure variable.
testWhileFalse2 = 
    let 
        myarg = while ("x":>Real) RFalse (c 5)
        dmyargx = rd ("z":>Real,myarg:>Real) $ (c 1) :* (c 3)
    in 
        runTermInProg dmyargx M.empty 

whileTrueTf = 
    let 
        iab = v "iab" -- ((i,a),b)
        iabpat = "iab" :> (Prod (Prod Real Real) Real)
        ia = fst (Prod Real Real,Real) iab
        i = fst (Real,Real) ia 
        a = snd (Real,Real) ia 
        b = snd (Prod Real Real,Real) iab
        guard = Pred LessThan (p $ (i , c 10) :> (Real,Real))
        w = while iabpat guard (
                ( p $ ((p $ (i:+ (c 1),a) :> (Real,Real)),b) :> (Prod Real Real,Real) )
            )
        whole = Let "iab" (Prod (Prod Real Real) Real) (Pair (Prod Real Real) Real (Pair Real Real (c 0.1) (c 0) ) (c 0)  ) w
    in 
        runTermInProg whole M.empty


dOfWhilexsquare = 
    let 
        guard = Pred LessThan (p $ (v "x",c 1.4) :> (Real,Real)) 
        w = while ("x":>Real) guard (
                call Times (p $ (v "x",v "x") :> (Real,Real))
            ) 
        whole = Let "x" Real (c 1.001) w
        rdwhole = rd ("x":>Real,w:>Real) $ (c 1.001) :* (c 1.51)
    in 
        -- [
        -- runTermInProg rdwhole M.empty
        -- ,
        whole
        -- rdwhole
        -- ,
        -- runTermInProg whole M.empty
        -- ]

dOfWhilexsquarePt2 = 
    let 
        guard = Pred LessThan (p $ (v "x",c 1.4) :> (Real,Real)) 
        w = while ("x":>Real) guard (
                call Times (p $ (v "x",v "x") :> (Real,Real))
            ) 
        whole = Let "x" Real (c 1.001) w
        rdwhole = rd ("x":>Real,w:>Real) $ (c 1.001) :* (c 1.51)
    in 
        -- [
        -- runTermInProg rdwhole M.empty
        -- ,
        -- whole
        -- rdwhole
        -- ,
        runTermInProg whole M.empty
        -- ]

dOfWhilexsquarePt3 = 
    let 
        guard = Pred LessThan (p $ (v "x",c 1.4) :> (Real,Real)) 
        w = while ("x":>Real) guard (
                call Times (p $ (v "x",v "x") :> (Real,Real))
            ) 
        whole = Let "x" Real (c 1.001) w
        rdwhole = rd ("x":>Real,w:>Real) $ (c 1.001) :* (c 1.001)
    in 
        -- [
        runTermInProg rdwhole M.empty
        -- ,
        -- whole
        -- rdwhole
        -- ,
        -- runTermInProg whole M.empty
        -- ]

prepareForSym t = injRawToRawR (gettyop instanceOpStruct1) t
dOfWhilexsquareSym = runSTVal (Interpreter.fullEvaluationSymbolic instanceOperationalStruct (prepareForSym dOfWhilexsquare)) (IS.IState M.empty M.empty [] "h" 0)

aReallySimpleTerm = 
    Let "x" Real (c 3) $ Let "x" Real (c 4) (v "x")
aReallySimpleTest = runTermInProg aReallySimpleTerm M.empty
dAReallySimpleTest = rd ("x":>Real,aReallySimpleTerm:>Real) $ (c 1) :* (c 5)

-- whiletest x = if x < 1.4 then whiletest (x*x) else x

whilesquared = 
    letrec "f" $ (Real:>Real) := \z -> (
        -- if z < 1.4
        let b = Pred LessThan (p $ (z,c 1.4):> (Real,Real)) in 
        let arg = call Times (p $ (z,z) :> (Real,Real)) in 
        iff b $ thenn (callf "f" arg) $ elsee z
    )

recursiveloopfalse = 
    letrec "f" $ (Real:>Real) := \z -> (
        -- if z < 1.4
        let b = Pred LessThan (p $ (z,c 1.4):> (Real,Real)) in 
        let arg = call Times (p $ (z,z) :> (Real,Real)) in 
        iff RFalse $ thenn (callf "f" arg) $ elsee z
    )

runSymbTermInProg term prog = runSTVal (Interpreter.fullEvaluationSymbolic instanceOperationalStruct term) (IS.IState prog M.empty [] "h" 0)
runwhilesquaredsym = runSymbTermInProg (callf "f" (c 1.001)) (program [whilesquared])

runrecursiveloopfalse = runSymbTermInProg (callf "f" (c 1.001)) (program [recursiveloopfalse])


whileFalseSymb = 
    let 
        myarg = while ("x":>Real) RFalse (c 5)
        dmyargx = rd ("x":>Real,myarg:>Real) $ (c 1) :* (c 3)
    in 
        runSymbTermInProg (prepareForSym myarg) M.empty
    
runwhilesquared = 
    let 
        myprog = program [whilesquared]
        myterm = callf "f" (c 1.001)
    in 
        runTermInProg myterm myprog

rundwhilesquared = 
    let 
        myprog = program [whilesquared]
        myterm = rd("z":>Real,callf "f" (v "z"):>Real) $ (c 1.001) :* (c 1.001)
    in 
        runTermInProg myterm myprog


timesTest = 
    let 
        timesself = call Times (p $ (v "x",v "y") :> (Real,Real))
        rtimeself = rd ("x":>Real,timesself:>Real) $ (c 5.001) :* (c 1.001)
        rtimeselfwhole = Let "y" Real (c 5) rtimeself
    in 
        runTermInProg rtimeselfwhole M.empty

-- So about this language: 
-- A more natural Times is provided here for reuse in programs as a sort of macro. 
-- Note that function symbols in SDPL are required to have exactly one parameter. 
-- In otherwords, when we form the term 
-- z :(R\x R) \proves (fst z) * (snd z):R
-- BUTTTT 
-- If we try to form 
-- x:R,y:R \proves x*y :R we can't really do that strictly speaking.  We have to do something like 
-- z : R\x R \proves fst z * snd z : R 
-----------------------------------------
-- x:R,y:R \proves let z = (x,y) in fst z * snd z : R
-- Thus a "more natural" version of times is 
-- given by this 
naturalTimes x y z = Let z (Prod Real Real) (p $ (Var x, Var y) :> (Real,Real))  $ Op Times (p $(fst (Real,Real) (Var z), snd (Real,Real) (Var z)) :> (Real,Real) )
timesTestWeird = 
    let 
        timesactual = naturalTimes "x" "y" "z" 
        rtimeinx = rd ("x":>Real,timesactual:>Real) $ (c 5.001) :* (c 1.001)
        nowbindy = Let "y" Real (c 5) rtimeinx
    in 
        runTermInProg nowbindy M.empty

squared = 
    letrec "f" $ (Real :> Real) := \z -> (
        let basic = Let "x" (Prod Real Real) (p $ (z,z) :> (Real,Real)) in 
        basic (Op Times (Var "x"))
    )

squaredTest = 
    let 
        myprog = program [squared]
        myarg = callf "f" (c 5)
        dermyarg = rd ("s":>Real,callf "f" (v "s"):>Real) $ (c 3) :* (c 4)
    in 
        runTermInProg dermyarg myprog



callOnWrongArgTest = 
    let 
        myprog = program [squared]
        derfinwrongarg = rd ("wrong":>Real,callf "f" (v "y"):>Real) $ (c 3) :* (c 4)
        bindytomakeaterm = Let "y" Real (c 17) derfinwrongarg
        dermyarg = rd ("wrong":>Real,bindytomakeaterm:>Real) $ (c 3) :* (c 4)
    in 
        runTermInProg bindytomakeaterm myprog
        -- interestingly if you differentiate again in the wrong variable, it takes a very long time to get 0 out.
        -- it really does seem that this should be an optimization here.

-- d(x.x^2)(1)(2) = 2*1*2 = 4
squaredTest2 =
    let 
        myterm = Let "x" (Prod Real Real) (p $ (v "z",v"z") :> (Real,Real)) (call Times (v "x"))
        myarg = rd ("z":>Real,myterm:>Real) $ (c 1) :* (c 2)
    in 
        runTermInProg myarg M.empty 

-- Let's actually get the output of a run of symbolic evaluation on a while loop.  Let's in fact, get the run for 

squaredTest3 =
    let 
        myterm = Let "x" (Prod Real Real) (p $ (v "z",v"z") :> (Real,Real)) (call Times (v "x"))
        myarg = rd ("z":>Real,myterm:>Real) $ (c 1) :* (c 3)
    in 
        runTermInProg myarg M.empty 

-- R[<1,1>](a,(b,c)) = b + c
rDelta = 
    let 
        arg1 = c 120 
        arg2 = p $ (c 3,c 4):> (Real, Real)
        arg12 = p $ (arg1,arg2) :> (Real, Prod Real Real)
        myterm = rd ("z":>Real,(p $ (v "z",v "z") :> (Real,Real)):> Prod Real Real) $ arg1 :* arg2 
    in 
        runTermInProg myterm M.empty

-- a better solution is to make a closure for times dfddd
-- recursive version

-- taking hte derivative of x*y with respect to (x,y) seems to work just fine.
times2 = 
    let 
        pt1 = call Times (p $ (fst (Real,Real) (v "xy"), snd (Real,Real) (v "xy")) :> (Real,Real)  )
        pt2 = Let "xy" (Prod Real Real) (p $ (c 1,c 2):> (Real, Real)) pt1
        pt3 = RD "xy" (Prod Real Real) Real pt1 (p $ (c 1,c 2):> (Real,Real)) (c 3)
    in 
        runTermInProg pt3 M.empty  

-- y = 4 in d(x.x*y)(1)*1 ~~> 4*1 = 4
times3 = 
    let 
        pt1 = Let "y" Real (c 4) $ RD "x" Real Real (Op Times (p $ (v "x",v "y") :> (Real,Real))) (c 1) (c 1)
    in 
        runTermInProg pt1 M.empty
    



module InterpreterTests where

import SDPLTerms 
import SDPLInterpreterOld

egEvTraceTerm1 = Let "x" (Const 3.0) (Op Sin (Var "x"))
egEvTraceTerm1Evald = fullEvaluationTermStrict "h" egEvTraceTerm1

sumsOfPairs = 
    Let "x" (Const 3.0) $ Let "y" (Const 2.0) $ Let "z" (Const 5.1) $ Let "w" (Const 18.0) $  (Pair (Var "x") (Var "y"))  :+ (Pair (Var "z") (Var "w"))
sumsOfPairsEvald = fullEvaluationTermStrict "h" sumsOfPairs

sumsOfPairsWithZeros = 
    let 
        xy = Pair (Var "x") (Var "y")
        zw = Pair (Var "z") (Var "w")
        xy0 = Pair xy Zero 
        zerozw = Pair Zero zw 
        sumthem = xy0 :+ zerozw 
    in
        Let "x" (Const 3.0) $ Let "y" (Const 2.0) $ Let "z" (Const 5.1) $ Let "w" (Const 18.0) sumthem 
sumsOfPairsWithZerosEvald = fullEvaluationTermStrict "h" sumsOfPairsWithZeros


egLetTest1 = Op  Times (Pair three four)
  where
    three = Let "y"  (Const 3.0) (Var "y")
    four = Let "y"  (Const 4.0) (Var "y")
-- This is (let y = 3 in y) * (let y = 4 in y) -- should evaluate to 3*4=12
getLetTest1Evald = fullEvaluationTermStrict  "y"  egLetTest1 
egLetTest2 = Let "y"  (Const 3.0) body 
  where
    body = Op Times (Pair  wyy five)
    wyy = Var "y"
    five = Let "y"  (Const 5.0) (Var "y")
-- This is let y = 3 in  y * (let y = 5 in y) -- should evaluate to 3*5=15
getLetTest2Evald = fullEvaluationTermStrict  "y"  egLetTest2
egWhile1 = Let "i"  (Const 0.1) $ While "i"  b1 m1 
  where
    b1 = P LessThan (Pair   (Var "i") (Const 25.0))
    m1 = (Var "i") :+ (Const 5.0)
-- This is 0.1 + 5 + 5 + 5 + 5 + 5 = 25.1
getWhileTest1Evald = fullEvaluationTermStrict "y"  egWhile1
egWhile2 = Let "n"  (Const 10.0) body 
  where
    body = Let "i"  (Const 0.1) $ While "i"  b1 m1
    b1 = P LessThan (Pair   (Var "i") (Var "n"))
    m1 = (Var "i") :+ (Const 5.0)
-- This is 0.1+5+5=10.1
getWhileTest2Evald = fullEvaluationTermStrict  "y"  egWhile2

egWhile5 r = Snd   $ Let "n"  (Const r) mainbody
  where 
    mainbody = Let "i"  (Const 0.0000000001) $ Let "f"  (Const 1.0) $ Let "if" (Pair  (Var "i") (Var "f")) body 
    body = While "if"  b1 m1
    b1 = P LessThan (Pair  (Fst  (Var "if")) (Var "n"))
    m1 = Let "i"  ((Fst  (Var "if")) :+ (Const 1.0)) m2 
    m2 = Let "f"  (Op times (Pair  (Snd  (Var "if")) (Var "i"))) m3 
    m3 = Pair  (Var "i") (Var "f")
    times =  Times 
    -- m1 = Pair Real Real ip1 ftip1 
    -- ip1 = (Fst Real Real (Var "if")) :+ (Const (R1 1))
    -- ftip1 = Op (Orig Times (Prod Real Real) Real) (Pair Real Real (Snd Real Real (Var "if")) ip1)
getWhile5 = fullEvaluationTermStrict  "y"  (egWhile5 5)
-- Note: This returns fac 170 instantly, in an interpreter.  So it's not sooo slow.
-- fac :: Double -> Err (ClosedVal Double)
fac r = fullEvaluationTermStrict  "y"  (egWhile5 r)

-- rd(x.sin(x))(3)*5
egDiff1 = RD "x"  (Op Sin (Var "x")) (Const 3.0) (Const 5.0)
egDiff1Evald = fullEvaluationTermStrict  "y"  egDiff1

-- let's do an iterated derivative ... to some really really high power
egDiff2 = 
  let 
    rtimes = RD "x" (Op Times (Var "x")) (Pair (Const 3.0) (Const 2.0)) (Const 4.0)
  in 
    rtimes 
  
-- should be (8,12) i.e. d(xy)/(x)(a,b)*r = br and dxy/y(a,b)*r = ar
egDiff2Eval2 = fullEvaluationTermStrict "y" egDiff2

-- while False f is a long variation of the identity function.  It should differentiate the 
-- same way.  Should be 3.0 then.
testWhileFalse = 
  let
    myarg = While "x" RFalse (Const 5.0)
    dmyargx = RD "x" myarg (Const 1.0) (Const 3.0)
  in 
    fullEvaluationTermStrict "y" dmyargx

dOfWhileSquare = 
  let 
    guard = P LessThan (Pair (Var "x") (Const 1.4))
    body = Op Times (Pair (Var "x") (Var "x"))
    w = While "x" guard body 
    whole = Let "x" (Const 1.001) w 
    rdwhole = RD "x" w (Const 1.001) (Const 1.001)
  in 
    fullEvaluationTermStrict "h" rdwhole 


-- put this one in a program and evaluate it in context.
-- Last thing to do: get the parser up and running and then we have rebuilt our language.
-- whilesquared = 
--     letrec "f" $ (Real:>Real) := \z -> (
--         -- if z < 1.4
--         let b = Pred LessThan (p $ (z,c 1.4):> (Real,Real)) in 
--         let arg = call Times (p $ (z,z) :> (Real,Real)) in 
--         iff b $ thenn (callf "f" arg) $ elsee z
--     )

-- recursiveloopfalse = 
--     letrec "f" $ (Real:>Real) := \z -> (
--         -- if z < 1.4
--         let b = Pred LessThan (p $ (z,c 1.4):> (Real,Real)) in 
--         let arg = call Times (p $ (z,z) :> (Real,Real)) in 
--         iff RFalse $ thenn (callf "f" arg) $ elsee z
--     )

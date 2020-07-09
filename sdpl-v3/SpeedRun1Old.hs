module Main where

import InterpreterTestsOld (dOfWhileSquare)

main :: IO ()
main = print dOfWhileSquare

-- ghc --make -O2 -ffun-to-thunk -fno-state-hack -funbox-strict-fields SpeedRun1
-- ghc --make -O2 -pgmlo opt-6.0 -pgmlc llc-6.0 -fllvm -fspecialize-aggressively -fstatic-argument-transformation -ffun-to-thunk -funbox-strict-fields -fworker-wrapper -fforce-recomp -fsimplifier-phases=8 SpeedRun1Old

{-
With 1.000001 and 1.000001 as "a" and "v"

Original Test:
real    0m14.381s
user    0m9.964s
sys     0m4.276s

So about 3 seconds faster than recursive.  Still we need to speed this up drastically. 
Need to figure out which source translation is faster for reverse differentiating while loops. 
Also need to figure out the meaning of differentiating "straight composition chains" 
Need to potentially keep bound variable information around at runtime.

With LLVM Optimizations:
real    0m10.167s
user    0m8.000s
sys     0m2.125s

With LLVM Optimizations after simple minded explicit variable checking in the RD loop:
real    0m0.021s
user    0m0.000s
sys     0m0.000s

And the while loop implementation is still faster than the recursive implementation in this variant; however, there is still something to be said for our improved way. 
And we can still really tweak the data structures involved and get things a lot faster.
-}
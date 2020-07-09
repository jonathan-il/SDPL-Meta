module Main where

import InterpreterTests (recdOfWhileSquare)

main :: IO ()
main = print recdOfWhileSquare

-- ghc --make -O2 -ffun-to-thunk -fno-state-hack -funbox-strict-fields SpeedRun2
-- ghc --make -O2 -pgmlo opt-6.0 -pgmlc llc-6.0 -fllvm -fspecialize-aggressively -fstatic-argument-transformation -ffun-to-thunk -funbox-strict-fields -fworker-wrapper -fforce-recomp -fsimplifier-phases=8 SpeedRun2

{-
With 1.000001 and 1.000001 as "a" and "v"

No significant difference with optimizations to the SpeedRun1

With LLVM Optimizations:
real    0m14.414s
user    0m10.656s
sys     0m3.719s

With freeness checking:
real    0m0.012s
user    0m0.000s
sys     0m0.000s

The only time now being spent on this program is the OS putting the process into the process table and scheduling it. 
Our program's exponential speedup is showing its teeth.
-}
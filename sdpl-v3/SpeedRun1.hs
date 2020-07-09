module Main where

import InterpreterTests (dOfWhileSquare)

main :: IO ()
main = print dOfWhileSquare

-- ghc --make -O2 -ffun-to-thunk -fno-state-hack -funbox-strict-fields SpeedRun1
-- ghc --make -O2 -pgmlo opt-6.0 -pgmlc llc-6.0 -fllvm -fspecialize-aggressively -fstatic-argument-transformation -ffun-to-thunk -funbox-strict-fields -fworker-wrapper -fforce-recomp -fsimplifier-phases=8 SpeedRun1


{-
With 1.000001 and 1.000001 as "a" and "v"

With LLVM Optimizations:
real    0m14.719s
user    0m11.391s
sys     0m3.266s

So slowed down to the old way of doing things pre-llvm optimizations.

With freeness checking:
real    0m0.012s
user    0m0.000s
sys     0m0.000s

That's an exponential speedup.
-}
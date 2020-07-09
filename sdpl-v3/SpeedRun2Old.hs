module Main where

import InterpreterTestsOld (recdOfWhileSquare)

main :: IO ()
main = print recdOfWhileSquare

-- ghc --make -O2 -ffun-to-thunk -fno-state-hack -funbox-strict-fields SpeedRun2
-- ghc --make -O2 -pgmlo opt-6.0 -pgmlc llc-6.0 -fllvm -fspecialize-aggressively -fstatic-argument-transformation -ffun-to-thunk -funbox-strict-fields -fworker-wrapper -fforce-recomp -fsimplifier-phases=8 SpeedRun2Old

{-
With: 1.000001 and 1.000001 as "a" and "v"

Original test:
real    0m17.316s
user    0m14.250s
sys     0m3.013s

With LLVM optimizations:
real    0m10.203s
user    0m7.859s
sys     0m2.250s

With LLVM Optimizations after simple minded explicit variable checking in the RD loop:
real    0m0.011s
user    0m0.000s
sys     0m0.016s

So now we see a real payoff.  Here we see that while still exponentially faster, the director string method is significantly faster.  And we didn't even 
choose an optimal way to implement the director strings.
-}
module Main where

import InterpreterTests (recdExcessive)

main :: IO ()
main = print recdExcessive

-- ghc --make -O2 -ffun-to-thunk -fno-state-hack -funbox-strict-fields SpeedRun4
-- ghc --make -O2 -pgmlo opt-6.0 -pgmlc llc-6.0 -fllvm -fspecialize-aggressively -fstatic-argument-transformation -ffun-to-thunk -funbox-strict-fields -fworker-wrapper -fforce-recomp -fsimplifier-phases=8 SpeedRun4

{-
With 1.0000000000000001 and 1.0000000000000001 as "a" and "v"

With LLVM-Optimizations:

Without LLVM-Optimizations:

-}
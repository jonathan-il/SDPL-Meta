module Main where

import InterpreterTests (dOfWhileSquareExcessive)

main :: IO ()
main = print dOfWhileSquareExcessive

-- ghc --make -O2 -ffun-to-thunk -fno-state-hack -funbox-strict-fields -fforce-recomp SpeedRun3
-- ghc --make -O2 -pgmlo opt-6.0 -pgmlc llc-6.0 -fllvm -fspecialize-aggressively -fstatic-argument-transformation -ffun-to-thunk -funbox-strict-fields -fworker-wrapper -fforce-recomp -fsimplifier-phases=8 SpeedRun3


{-
With 1.0000000000000001 and 1.0000000000000001

With LLVM Optimizations:


Without LLVM Optimizations

-}
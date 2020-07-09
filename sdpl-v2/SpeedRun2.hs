module Main where

import InterpreterTests (recdOfWhileSquare)

main :: IO ()
main = print recdOfWhileSquare

-- ghc --make -O2 -ffun-to-thunk -fno-state-hack -funbox-strict-fields SpeedRun2
{-
real    0m17.316s
user    0m14.250s
sys     0m3.013s
with 1.000001 and 1.000001 as "a" and "v"
-}
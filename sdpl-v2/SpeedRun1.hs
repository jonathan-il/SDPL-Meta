module Main where

import InterpreterTests (dOfWhileSquare)

main :: IO ()
main = print dOfWhileSquare

-- ghc --make -O2 -ffun-to-thunk -fno-state-hack -funbox-strict-fields SpeedRun1


{-
real    0m14.381s
user    0m9.964s
sys     0m4.276s
with 1.000001 and 1.000001 as "a" and "v"
So about 3 seconds faster than recursive.  Still we need to speed this up drastically. 
Need to figure out which source translation is faster for reverse differentiating while loops. 
Also need to figure out the meaning of differentiating "straight composition chains" 
Need to potentially keep bound variable information around at runtime.
-}
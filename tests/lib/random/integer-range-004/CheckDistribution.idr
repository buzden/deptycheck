module CheckDistribution

import Data.Bits
import Data.List

import DistrCheckCommon

import System.Random.Pure.StdGen

%default total

L, R : Integer
L = -1
R = 1

ll, rr : Integer
ll = L `min` R
rr = L `max` R

cnt : Nat
cnt = S $ cast $ rr - ll

main : IO ()
main = printVerdict !initStdGen (randomR (L, R)) $
         iterateN (1000 `min` cnt) (+1) ll <&> \n =>
           coverWith (ratio 1 cnt) (== n)

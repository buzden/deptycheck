module CheckDistribution

import Data.Bits
import Data.List

import DistrCheckCommon

import System.Random.Pure.StdGen

%default total

L, R : Int64
L = 9223372036854775807
R = 9223372036854775803

ll, rr : Int64
ll = L `min` R
rr = L `max` R

cnt : Nat
cnt = S $ cast $ rr - ll

main : IO ()
main = printVerdict !initStdGen (randomR (L, R)) $
         iterateN (1000 `min` cnt) (+1) ll <&> \n =>
           coverWith (ratio 1 cnt) (== n)

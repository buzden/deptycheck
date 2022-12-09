module CheckDistribution

import Data.Bits
import Data.List

import DistrCheckCommon

import System.Random.Pure.StdGen

%default total

L, R : Bits64
L = 18446744073709551615
R = 18446744073709551610

ll, rr : Bits64
ll = L `min` R
rr = L `max` R

cnt : Nat
cnt = S $ cast $ rr - ll

main : IO ()
main = printVerdict !initStdGen (randomR (L, R)) $
         iterateN cnt (+1) ll <&> \n =>
           coverWith (ratio 1 cnt) (== n)

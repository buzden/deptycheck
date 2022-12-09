module CheckDistribution

import Data.Bits
import Data.List

import DistrCheckCommon

import System.Random.Pure.StdGen

%default total

L, R : Integer
L = 9223372036854775807
R = 9223372036854775803

ll, rr : Integer
ll = L `min` R
rr = L `max` R

cnt : Nat
cnt = S $ cast $ rr - ll

main : IO ()
main = printVerdict !initStdGen (randomR {a=Nat} (cast L, cast R)) $
         iterateN (1000 `min` cnt) (+1) ll <&> \n =>
           coverWith (ratio 1 cnt) (== cast n)

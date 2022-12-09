module CheckDistribution

import Data.Bits
import Data.List

import DistrCheckCommon

import System.Random.Pure.StdGen

%default total

N : Nat
N = 100000

St, D : Fin $ S N
St = 2000
D = 0

main : IO ()
main = printVerdict !initStdGen (randomR {a=Fin $ S N} (St, St + D)) $
         iterateN (S $ finToNat D) finS St <&> \n =>
           coverWith (ratio 1 $ S $ finToNat D) (== n)

module CheckDistribution

import Data.Bits
import Data.List

import DistrCheckCommon

import System.Random.Pure.StdGen

%default total

N : Nat
N = 100000

main : IO ()
main = printVerdict !initStdGen (random {a=Fin $ S N}) $
         iterateN 100 finS 2000 <&> \n =>
           coverWith (ratio 1 $ S N) (== n)

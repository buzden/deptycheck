module CheckDistribution

import Data.Bits
import Data.List1

import DistrCheckCommon

import System.Random.Pure.StdGen

%default total

N : Nat
N = 10

main : IO ()
main = printVerdict !initStdGen (random {a=Fin $ S N}) $
         forget (allFins {n=N}) <&> \n =>
           coverWith (ratio 1 $ S N) (== n)

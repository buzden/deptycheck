module CheckDistribution

import Data.Bits
import Data.List

import DistrCheckCommon

import System.Random.Pure.StdGen

%default total

L, R : Bits64
L = 19997
R = 166021

main : IO ()
main = printVerdict !initStdGen (randomR (L, R)) $
         [L .. R] <&> \n =>
           coverWith (ratio 1 $ S $ cast $ R - L) (== n)

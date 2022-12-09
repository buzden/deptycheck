module CheckDistribution

import Data.Bits
import Data.List1

import DistrCheckCommon

import System.Random.Pure.StdGen

%default total

main : IO ()
main = printVerdict !initStdGen (random {a=Bits64}) $
         forget (allFins {n=63}) >>= \b =>
           [ coverWith 50.percent $ (== True)  . (`testBit` b)
           , coverWith 50.percent $ (== False) . (`testBit` b)
           ]

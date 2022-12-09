module CheckDistribution

import Data.Bits
import Data.List1

import DistrCheckCommon

import System.Random.Pure.StdGen

%default total

main : IO ()
main = printVerdict (random {a=Bool}) !initStdGen $
         [ coverWith 50.percent $ (== True)
         , coverWith 50.percent $ (== False)
         ]

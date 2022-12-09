module CheckDistribution

import Data.Bits
import Data.List1

import DistrCheckCommon

import System.Random.Pure.StdGen

%default total

main : IO ()
main = printVerdict !initStdGen (random {a=Integer})
         [ coverWith 50.percent (< 0)
         , coverWith 50.percent (> 0)
         ]

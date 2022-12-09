module CheckDistribution

import Data.Bits
import Data.List1

import DistrCheckCommon

import System.Random.Pure.StdGen

%default total

main : IO ()
main = printVerdict !initStdGen (random {a=Double})
         [ coverWith 100.percent (<= 1.0)
         , coverWith 100.percent (>= 0.0)
         ]

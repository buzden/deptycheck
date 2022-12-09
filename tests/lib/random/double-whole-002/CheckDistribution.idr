module CheckDistribution

import Data.Bits
import Data.List1

import DistrCheckCommon

import System.Random.Pure.StdGen

%default total

main : IO ()
main = printVerdict !initStdGen (random {a=Double}) $
         [the Nat 0 .. 7] >>= \r =>
           [0 .. r] <&> \c =>
             coverWith (ratio 1 $ S r) $ \x =>
               x >= cast c / cast (S r) && x <= cast (S c) / cast (S r)

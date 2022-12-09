module CheckDistribution

import Data.Bits
import Data.List1

import DistrCheckCommon

import System.Random.Pure.StdGen

%default total

ll, rr : Double
ll = 1.79769e-30
rr = -1.56321e-10

L, R : Double
L = ll `min` rr
R = ll `max` rr

D : Double
D = R - L

-- [0, 1] -> [L, R]
stretch : Double -> Double
stretch x = x * D + L

main : IO ()
main = printVerdict !initStdGen (randomR (L, R)) $
         [the Nat 0 .. 7] >>= \r =>
           [0 .. r] <&> \c =>
             coverWith (ratio 1 $ S r) $ \x =>
               x >= stretch (cast c / cast (S r)) && x <= stretch (cast (S c) / cast (S r))

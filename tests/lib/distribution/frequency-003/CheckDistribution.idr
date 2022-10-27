module CheckDistribution

import DistrCheckCommon

%default total

-- Some big prime numbers
a, b : Nat
a = 100000007
b = 100000217

bools : Gen Bool
bools = frequency
          [ (a, pure True)
          , (b, pure False)
          ]

main : IO ()
main = printVerdict bools
         [ coverWith (ratio a (a + b)) (== True)
         , coverWith (ratio b (a + b)) (== False)
         ]

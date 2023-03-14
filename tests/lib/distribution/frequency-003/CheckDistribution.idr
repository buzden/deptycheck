module CheckDistribution

import DistrCheckCommon

%default total

bools : Gen0 Bool
bools = frequency
          [ (100000007, pure True)
          , (100000217, pure False)
          ]
        -- weights are prime numbers
        -- percentage below should be in default tolerance of 95%

main : IO ()
main = printVerdict bools
         [ coverWith 50.percent (== True)
         , coverWith 50.percent (== False)
         ]

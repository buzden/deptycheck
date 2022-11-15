module CheckDistribution

import DistrCheckCommon

%default total

bools : Gen Bool
bools = frequency
          [ (1, pure True)
          , (100000000, pure False)
          ]

main : IO ()
main = printVerdict bools
         [ coverWith 1.0e-8 (== True)
         , coverWith 100.percent (== False)
         ]

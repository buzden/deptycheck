module CheckDistribution

import DistrCheckCommon

%default total

bools : Gen CanBeEmptyStatic Bool
bools = frequency
          [ (100000000, pure True)
          , (100000000, pure False)
          ]

main : IO ()
main = printVerdict bools
         [ coverWith 50.percent (== True)
         , coverWith 50.percent (== False)
         ]

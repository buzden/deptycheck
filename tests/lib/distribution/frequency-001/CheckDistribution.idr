module CheckDistribution

import DistrCheckCommon

%default total

bools : Gen CanBeEmptyStatic Bool
bools = frequency
          [ (1, pure True)
          , (2, pure False)
          ]

main : IO ()
main = printVerdict bools
         [ coverWith 33.percent (== True)
         , coverWith 66.percent (== False)
         ]

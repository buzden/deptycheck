module CheckDistribution

import DistrCheckCommon

%default total

bools : Gen0 Bool
bools = elements [True, False]

-- intentionally wrong expected values
main : IO ()
main = printVerdict bools
  [ coverWith 25.percent (== True)
  , coverWith 75.percent (== False)
  ]

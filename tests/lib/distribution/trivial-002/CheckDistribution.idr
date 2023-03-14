module CheckDistribution

import DistrCheckCommon

%default total

bools : Gen0 Bool
bools = elements [True]

main : IO ()
main = printVerdict bools [coverWith 100.percent (== True), coverWith 0.percent (== False)]

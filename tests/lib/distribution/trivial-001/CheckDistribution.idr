module CheckDistribution

import DistrCheckCommon

%default total

bools : Gen CanBeEmptyStatic Bool
bools = elements [True, False]

main : IO ()
main = printVerdict bools [coverWith 50.percent (== True), coverWith 50.percent (== False)]

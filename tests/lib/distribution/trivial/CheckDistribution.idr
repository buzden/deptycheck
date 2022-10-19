module CheckDistribution

import Data.List.Lazy

import Test.DepTyCheck.Gen

import Statistics.Confidence

%default total

bools : Gen Bool
bools = elements [True, False]

-- we expect verdict to contain only `Just True`
verdict = head' $ filter (all isJust) $
            checkCoverageConditions [coverWith 50.percent (== True), coverWith 50.percent (== False)] $
              unGenTryN 10000000 someStdGen bools

main : IO ()
main = putStrLn $ show verdict

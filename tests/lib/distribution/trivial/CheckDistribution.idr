module CheckDistribution

import Data.List.Lazy

import Test.DepTyCheck.Gen

import Statistics.Confidence

%default total

bools : Gen Bool
bools = elements [True, False]

verdict : Vect n (CoverageTest a) -> Gen a -> Bool
verdict conds = not . null . filter (all isJust) .
                  checkCoverageConditions conds . unGenTryN 10000000 someStdGen

printVerdict : HasIO m => Gen a -> Vect n (CoverageTest a) -> m ()
printVerdict = putStrLn .: show .: flip verdict

main : IO ()
main = printVerdict bools [coverWith 50.percent (== True), coverWith 50.percent (== False)]

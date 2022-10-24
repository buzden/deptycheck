module DistrCheckCommon

import Data.List.Lazy

import public Test.DepTyCheck.Gen

import public Statistics.Confidence

%default total

verdict : Vect n (CoverageTest a) -> Gen a -> Bool
verdict conds = not . null . filter (all isJust) .
                  checkCoverageConditions conds . unGenTryN 10000000 someStdGen

export
printVerdict : HasIO m => Gen a -> Vect n (CoverageTest a) -> m ()
printVerdict = putStrLn .: show .: flip verdict

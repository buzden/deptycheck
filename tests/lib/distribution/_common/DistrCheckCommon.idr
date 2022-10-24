module DistrCheckCommon

import Data.List.Lazy

import public Test.DepTyCheck.Gen

import public Statistics.Confidence

%default total

verdict : Vect n (CoverageTest a) -> Gen a -> Maybe $ Vect n Bool
verdict conds = head' . mapMaybe sequence .
                  checkCoverageConditions conds . unGenTryN 10000000 someStdGen

export
printVerdict : HasIO m => Gen a -> Vect n (CoverageTest a) -> m ()
printVerdict = putStrLn .: show .: flip verdict

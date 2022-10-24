module DistrCheckCommon

import Data.List.Lazy

import public Test.DepTyCheck.Gen

import public Statistics.Confidence

%default total

verdict : Vect n (CoverageTest a) -> Gen a -> Maybe $ Vect n SignificantBounds
verdict conds = head' . mapMaybe sequence . drop 100 . {- this dropping is a hack for managing low precision at the very beginning -}
                  checkCoverageConditions conds . unGenTryN 10000000 someStdGen

Show SignificantBounds where show = interpolate

export
printVerdict : HasIO m => Gen a -> Vect n (CoverageTest a) -> m ()
printVerdict = putStrLn .: show .: flip verdict

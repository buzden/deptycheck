module DistrCheckCommon

import Data.List.Lazy

import public Test.DepTyCheck.Gen

import public Statistics.Norm.Precise
import public Statistics.Confidence

import System.Random.Pure.StdGen

%default total

find : LazyList (Vect n SignificantBounds) -> Maybe $ Vect n SignificantBounds
find [] = Nothing
find (x::xs) = case force xs of
                 [] => Just x
                 xs => if all isOk x then Just x else assert_total $ find xs

verdict : (a -> Maybe b) -> Vect n (CoverageTest b) -> Gen em a -> Maybe $ Vect n SignificantBounds
verdict f conds = find . mapMaybe sequence . checkCoverageConditions conds . mapMaybe f . unGenTryN 10000000 someStdGen

Show SignificantBounds where show = interpolate

export
printVerdict' : HasIO m => (a -> Maybe b) -> Gen em a -> Vect n (CoverageTest b) -> m ()
printVerdict' mapper = putStrLn .: show .: flip (verdict mapper)

export %inline
printVerdict : HasIO m => Gen em a -> Vect n (CoverageTest a) -> m ()
printVerdict = printVerdict' Just

module DistrCheckCommon

import Data.Fuel
import Data.List.Lazy
import Data.Stream

import public Statistics.Confidence

%default total

find : LazyList (Vect n SignificantBounds) -> Maybe $ Vect n SignificantBounds
find [] = Nothing
find (x::xs) = case force xs of
                 [] => Just x
                 xs => if all isOk x then Just x else assert_total $ find xs

verdict : Vect n (CoverageTest a) -> Stream a -> Maybe $ Vect n SignificantBounds
verdict conds = find . mapMaybe sequence .
                  checkCoverageConditions conds . take (limit 10000000)

Show SignificantBounds where show = interpolate

export
printVerdict : HasIO m => g -> (g -> (g, a)) -> List (CoverageTest a) -> m ()
printVerdict st it cts = putStrLn $ show $ verdict (fromList cts) (unfoldr (swap . it) st)

module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

import Data.Fin

%default total

data Y : (n : Nat) -> Fin n -> Type where
  Y0 : Y 1 i
  Y2 : Y 3 2

data X : Type where
  MkX : Y n i -> X

isY0 : X -> Bool
isY0 $ MkX Y0 = True
isY0 _        = False

isY2 : X -> Bool
isY2 $ MkX Y2 = True
isY2 _        = False

genX : Fuel -> Gen MaybeEmpty X
genX = deriveGen

-- Check that constructors of `Y` in `X` are uniformly distributed

mainFor : (fuel : Fuel) -> IO ()
mainFor fuel = printVerdict (genX fuel) $ fromList
                 $ [ coverWith (ratio 1 2) f | f <- [isY0, isY2] ]

main : IO ()
main = do
  mainFor $ limit 2
  mainFor $ limit 3
  mainFor $ limit 100

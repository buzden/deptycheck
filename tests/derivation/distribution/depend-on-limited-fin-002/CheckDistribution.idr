module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

import Data.Fin

%default total

data X : (n : Nat) -> Type where
  X0 : X 1
  X2 : X 3

data Y : (n : Nat) -> Fin n -> Type where
  Y0 : Y 1 i
  Y2 : Y 3 2

data Z : Type where
  MkZ : (n : Nat) -> (i : Fin n) -> (x : X n) -> (y : Y n i) -> Z

isY0 : Z -> Bool
isY0 $ MkZ {y=Y0, _} = True
isY0 _               = False

isY2 : Z -> Bool
isY2 $ MkZ {y=Y2, _} = True
isY2 _               = False

genZ : Fuel -> Gen MaybeEmpty Z
genZ = deriveGen

-- Check that constructors of `Y` in `Z` are uniformly distributed

mainFor : (fuel : Fuel) -> IO ()
mainFor fuel = printVerdict (genZ fuel) $ fromList
                 $ [ coverWith (ratio 1 2) f | f <- [isY0, isY2] ]

main : IO ()
main = do
  mainFor $ limit 2
  mainFor $ limit 3
  mainFor $ limit 100

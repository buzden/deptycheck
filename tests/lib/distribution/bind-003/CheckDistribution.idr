module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

-- Credits for this test to Aleksei Volkov @AlgebraicWolf

f : Bool -> Gen MaybeEmpty Bool
f False = empty
f True  = pure True

notEmpty : Gen MaybeEmpty Bool
notEmpty = oneOf [pure True, pure False] >>= f

notEmpty' : Gen MaybeEmpty Bool
notEmpty' = oneOf [pure True] >>= f

main : IO ()
main = do
  printVerdict notEmpty  [ coverWith 1 (== True) ]
  printVerdict notEmpty' [ coverWith 1 (== True) ]

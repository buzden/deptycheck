module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

f : Bool -> Bool
f = const True

notEmpty : Gen MaybeEmpty Bool
notEmpty = pure f <*> oneOf [pure True, pure False]

notEmpty' : Gen MaybeEmpty Bool
notEmpty' = oneOf [pure f, empty] <*> oneOf [pure True, pure False]

notEmpty'' : Gen MaybeEmpty Bool
notEmpty'' = oneOf [empty, pure f] <*> oneOf [pure True, pure False]

main : IO ()
main = do
  printVerdict notEmpty   [ coverWith 1 (== True) ]
  printVerdict notEmpty'  [ coverWith 1 (== True) ]
  printVerdict notEmpty'' [ coverWith 1 (== True) ]

module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

f : (n : Nat) -> Gen MaybeEmpty Bool
f 1  = pure True
f 10 = pure False
f _  = empty

g : Gen MaybeEmpty $ Maybe Bool
g = choose (1, 100) >>= \_ => oneOf
  [ pure Nothing
  , elements [1 .. 30] >>= f <&> Just
  ]

main : IO ()
main = do
  printVerdict g
    [ coverWith (ratio 1 2) (== Nothing)
    , coverWith (ratio 1 4) (== Just True)
    , coverWith (ratio 1 4) (== Just False)
    ]

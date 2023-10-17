module DerivedGen

import AlternativeCore
import RunDerivedGen

import Data.Vect

%default total

%language ElabReflection

data X : (a : Type) -> a -> a -> Type where
  E : X a x x

{a : Type} -> {x, y : a} -> Show a => Show (X a x y) where
  show E = "E \{show x} \{show y}"

-- `DecEq a` must go after the declaration of the `a : Type` parameter.
-- If `a` parameter must go after the `Fuel` parameter, then `DecEq a` must go after it, too.
-- Or `a` parameter should be on the left of `Fuel` parameter together with the `DecEq a` one.
checkedGen : DecEq a => Fuel -> (x, y : a) -> Gen MaybeEmpty (X a x y)
--checkedGen : Fuel -> (a : Type) -> (x, y : a) -> DecEq a => Gen MaybeEmpty (X a x y)
checkedGen = deriveGen {core=EmptyCons}

main : IO Unit
main = runGs
  [ G $ \fl => checkedGen fl Nat 0 0
  , G $ \fl => checkedGen fl Nat 0 1
  , G $ \fl => checkedGen fl String "a" "a"
  ]

module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data EqA : (a : Type) -> a -> a -> Type where
  MkEqA : {x, y : b} -> (x = y) -> EqA b x y

Show (EqA a x y) where
  show _ = "Refl"

checkedGen : DecEq a => Fuel -> (x, y : a) -> Gen MaybeEmpty (EqA a x y)
checkedGen = deriveGen

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl (the Nat 0) 0
  , G $ \fl => checkedGen fl (the Nat 4) 3
  , G $ \fl => checkedGen fl (the Nat 4) 4
  , G $ \fl => checkedGen fl False True
  , G $ \fl => checkedGen fl False False
  , G $ \fl => checkedGen fl "" ""
  , G $ \fl => checkedGen fl "ab" "ab"
  , G $ \fl => checkedGen fl "ab" "ba"
  ]

module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

checkedGen : DecEq a => Fuel -> (x, y : a) -> Gen MaybeEmpty (x = y)
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

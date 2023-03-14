module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

Show (Gen x) where
  show _ = "a generator"

checkedGen : Fuel -> (a : Type) -> Gen0 $ Gen0 a
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl Nat ]

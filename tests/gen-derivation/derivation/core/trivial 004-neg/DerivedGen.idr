module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

Show (Gen em x) where
  show _ = "a generator"

checkedGen : Fuel -> (em : _) -> (a : Type) -> Gen CanBeEmptyStatic $ Gen em a
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl CanBeEmptyStatic Nat ]

module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

Show (Gen em x) where
  show _ = "a generator"

checkedGen : Fuel -> (em : _) -> (a : Type) -> Gen MaybeEmpty $ Gen em a
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl MaybeEmpty Nat ]

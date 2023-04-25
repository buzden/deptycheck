module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

Show (x ** Gen CanBeEmptyStatic x) where
  show _ = "a generator"

checkedGen : Fuel -> (em : _) -> Gen CanBeEmptyStatic (a ** Gen em a)
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl CanBeEmptyStatic ]

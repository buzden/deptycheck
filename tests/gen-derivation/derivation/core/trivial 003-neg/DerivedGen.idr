module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

Show (x ** Gen CanBeEmptyStatic x) where
  show _ = "a generator"

checkedGen : Fuel -> Gen CanBeEmptyStatic (a ** Gen CanBeEmptyStatic a)
checkedGen = deriveGen

main : IO ()
main = runGs [ G checkedGen ]

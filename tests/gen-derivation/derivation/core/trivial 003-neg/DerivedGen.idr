module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

Show (x ** Gen0 x) where
  show _ = "a generator"

checkedGen : Fuel -> Gen0 (a ** Gen0 a)
checkedGen = deriveGen

main : IO ()
main = runGs [ G checkedGen ]

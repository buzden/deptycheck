module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

Show (x ** Gen x) where
  show _ = "a generator"

checkedGen : Fuel -> Gen (a ** Gen a)
checkedGen = deriveGen

main : IO ()
main = runGs [ G checkedGen ]

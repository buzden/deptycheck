module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X = MkX String

checkedGen : Fuel -> Gen MaybeEmpty X
checkedGen = deriveGen

Show X where
  show (MkX s) = "MkX \{show s}"

main : IO ()
main = runGs [ G checkedGen ]

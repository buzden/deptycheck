module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> Gen MaybeEmpty Void
checkedGen = deriveGen

main : IO ()
main = runGs [ G checkedGen ]

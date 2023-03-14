module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> Gen0 (Maybe Bool)
checkedGen = deriveGen

main : IO ()
main = runGs [ G checkedGen ]

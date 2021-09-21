module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> Gen Bool
--checkedGen = deriveGen
checkedGen = const empty

main : IO ()
main = runGs [ G checkedGen ]

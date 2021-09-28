module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> Gen Unit
--checkedGen = deriveGen
checkedGen = const empty

main : IO ()
main = runGs [ G $ \fl => checkedGen fl ]

module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> Gen CanBeEmptyStatic Unit
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl ]

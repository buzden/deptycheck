module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> Gen MaybeEmpty Nat
checkedGen = deriveGen @{LeastEffort}

main : IO ()
main = runGs [ G $ \fl => checkedGen fl ]

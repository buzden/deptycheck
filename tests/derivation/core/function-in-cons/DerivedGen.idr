module DerivedGen

import RunDerivedGen

%default total

data X : Type where
  MkX : (Unit -> Unit) -> X

Show X where
  show (MkX f) = "MkX f"

%language ElabReflection

checkedGen : Fuel -> Gen MaybeEmpty X
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]

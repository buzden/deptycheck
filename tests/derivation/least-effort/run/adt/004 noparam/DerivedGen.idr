module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X : Type where
  E : X
  R : X -> Nat -> X

Show X where
  show E = "E"
  show (R x n) = "R (\{show x}) \{show n}"

checkedGen : Fuel -> Gen MaybeEmpty X
checkedGen = deriveGen @{LeastEffort}

main : IO ()
main = runGs [ G $ \fl => checkedGen fl ]

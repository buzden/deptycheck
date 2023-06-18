module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

-- both type arguments are parameters, not indices
data X : Bool -> Bool -> Type where
  X0 : (b1 : Bool) -> (b2 : Bool) -> X b1 b2
  X1 : X b1 b2

Show (X b1 b2) where
  show (X0 b1 b2) = "X0 \{show b1} \{show b2}"
  show X1         = "X1"

checkedGen : Fuel -> Gen MaybeEmpty (b1 ** b2 ** X b1 b2)
checkedGen = deriveGen

main : IO ()
main = runGs
  [ G checkedGen
  ]

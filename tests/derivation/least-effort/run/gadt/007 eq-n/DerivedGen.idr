module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%language ElabReflection

data EqualN : Nat -> Nat -> Type where
  ReflN : EqualN x x

{a, b : Nat} -> Show (EqualN a b) where
  show ReflN = "ReflN : EqualN \{show a} \{show b}"

checkedGen : Fuel -> Gen MaybeEmpty (a ** b ** EqualN a b)
checkedGen = deriveGen @{LeastEffort}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]

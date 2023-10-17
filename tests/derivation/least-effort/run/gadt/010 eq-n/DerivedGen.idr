module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%language ElabReflection

data EqualN : Nat -> Nat -> Type where
  ReflN : EqualN x x

{a, b : Nat} -> Show (EqualN a b) where
  show ReflN = "ReflN : EqualN \{show a} \{show b}"

checkedGen : Fuel -> (a, b : Nat) -> Gen MaybeEmpty $ EqualN a b
checkedGen = deriveGen @{LeastEffort}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 5 0
  , G $ \fl => checkedGen fl 5 5
  , G $ \fl => checkedGen fl 0 1
  , G $ \fl => checkedGen fl 0 0
  , G $ \fl => checkedGen fl 11 12
  , G $ \fl => checkedGen fl 12 12
  ]

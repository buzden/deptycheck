module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%language ElabReflection

data LT2 : Nat -> Nat -> Type where
  Base : x `LT2` S (S x)
  Step : x `LT2` y -> x `LT2` S y

show' : (a, b : Nat) -> LT2 x y -> String
show' a b Base      = "! \{show a} <<= \{show b}"
show' a b $ Step lt = ".\{show' a b lt}"

{a, b : Nat} -> Show (LT2 a b) where
  show = show' a b

checkedGen : Fuel -> (a : Nat) -> Gen MaybeEmpty (b ** LT2 a b)
checkedGen = deriveGen @{LeastEffort}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 0
  , G $ \fl => checkedGen fl 1
  , G $ \fl => checkedGen fl 2
  , G $ \fl => checkedGen fl 14
  , G $ \fl => checkedGen fl 23
  ]

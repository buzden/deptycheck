module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Fin n -> Type where
  MkX : (n : _) -> (f : Fin n) -> X (FS (FS f))

Show (X f) where
  show $ MkX n f = "MkX \{show n} \{show f}"

%language ElabReflection

checkedGen : Fuel -> (n : Nat) -> (f : Fin n) -> Gen MaybeEmpty $ X f
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 3 0
  , G $ \fl => checkedGen fl 5 4
  ]

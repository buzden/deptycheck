module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

record R where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
  f : Nat

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R

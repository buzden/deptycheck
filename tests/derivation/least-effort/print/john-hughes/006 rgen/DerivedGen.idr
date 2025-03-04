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
  {auto cd : So $ c == d}
  {auto be : So $ b == e}
  {auto af : So $ a == f}
  {auto bc : So $ b == c}
  {auto ab : So $ a == b}

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R

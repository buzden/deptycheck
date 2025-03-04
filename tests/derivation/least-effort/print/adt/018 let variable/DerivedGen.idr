module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : String -> Nat -> Type where
  MkX : (n : _) -> (m : _) -> X n m

data Y : Nat -> Type where
  MkY : (u : Nat) -> forall n, m, k. let xx = S in X n (xx m) -> X n (xx k) -> Y (xx u)

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => (n : Nat) -> Gen MaybeEmpty $ Y n

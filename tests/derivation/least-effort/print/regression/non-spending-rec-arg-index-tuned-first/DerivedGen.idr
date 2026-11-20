module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : Nat -> Type where
  L : X n
  N : (k : Nat) -> X k -> X n -> X (S n)

GenOrderTuning `{N}.dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [`{k}]

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => (n : Nat) -> Gen MaybeEmpty (X n)

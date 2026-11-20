module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : Nat -> Type where
  Leaf : X 0
  Bal  : X n -> X n -> X (S n)
  LH   : X (S n) -> X n -> X (S (S n))
  RH   : X n -> X (S n) -> X (S (S n))

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (n : Nat) -> Gen MaybeEmpty (X n)

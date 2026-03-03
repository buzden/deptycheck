module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : (Nat -> Nat) -> Type where
  Z : X S
  Y : X f -> X $ f . S

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (f ** X f)

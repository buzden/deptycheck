module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : Type -> Type where
  Z : X Nat
  Y : X t -> X $ List t

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (t ** X t)

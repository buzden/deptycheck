module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : Nat -> Type where
  MkX : {n : _} -> X n

data Y : Type where
  MkY : X n -> Y

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Y

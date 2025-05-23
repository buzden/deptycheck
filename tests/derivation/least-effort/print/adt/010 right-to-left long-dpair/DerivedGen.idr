module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : Nat -> Nat -> Type where
  MkX : {n : _} -> {m : _} -> X n m

data Y : Type where
  MkY : X n m -> Y

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Y

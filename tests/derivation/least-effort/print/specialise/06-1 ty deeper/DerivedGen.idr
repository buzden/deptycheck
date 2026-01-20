module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data Y : Type -> Type where
  MkY : Either Nat a -> Y a

data X : Type where
  MkX : Either Nat (Y $ Either (Fin 5) String) -> X

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty X

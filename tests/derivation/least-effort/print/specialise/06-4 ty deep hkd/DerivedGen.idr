module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data Z : Type -> Type where
  MkZ : Either Nat a -> Z a

data Y : (Type -> Type) -> Type -> Type where
  MkY : Either (f a) (f $ f a) -> Y f a

data X : Type where
  MkX : Y Z Nat -> X

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X

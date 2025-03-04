module DerivedGen

import Data.Fin

import Deriving.DepTyCheck.Gen

%default total

data X : Fin n -> Type where
  MkX : (n : _) -> (f : Fin n) -> X (FS f)

%language ElabReflection

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (n : Nat) -> (f : Fin n) -> Gen MaybeEmpty $ X f

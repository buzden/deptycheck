module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : Nat -> Type where
  MkX : Vect n (Fin m) -> X m

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (m : _) -> Gen MaybeEmpty $ X m

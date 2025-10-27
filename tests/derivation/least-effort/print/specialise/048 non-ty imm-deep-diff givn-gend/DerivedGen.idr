module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : Nat -> Nat -> Type where
  MkX : Vect n (Fin m) -> X n m

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (m : _) -> Gen MaybeEmpty (n ** X n m)

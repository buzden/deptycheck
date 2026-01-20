module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : Nat -> Type where
  MkX : Vect n String -> X n

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty String) => (n : _) -> Gen MaybeEmpty $ X n

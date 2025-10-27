module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : Type where
  MkX : Vect n (Fin n) -> Either (n `LT` m) (m `LT` n) => X

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X

module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : Type where
  E : X
  R : X -> Nat -> X

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X

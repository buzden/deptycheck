module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : Type -> Type where
  MkX : Nat -> List a -> X a

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty (t ** List t)) => Gen MaybeEmpty (t ** X t)

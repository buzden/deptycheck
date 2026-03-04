module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : (b : Bool) -> (b = True) -> Type where
  XT : X True Refl
  XF : X True Refl

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (a ** b ** X a b)

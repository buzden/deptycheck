module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : (b : Bool) -> (if b then Unit else Nat) -> Type where
  XT : X True ()
  XF : X False n

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (a ** b ** X a b)

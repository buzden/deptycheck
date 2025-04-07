module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data Z : Fin n -> Fin m -> Type where
  MkZ : Z {n = S n} {m = 2} 0 1

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (m ** g : Fin m ** n ** f : Fin n ** Z f g)

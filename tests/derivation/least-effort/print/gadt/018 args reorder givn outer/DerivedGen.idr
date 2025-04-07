module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data Z : Fin n -> Fin m -> Type where
  MkZ : Z {n = S n} {m = 2} 0 1

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (m : _) -> (g : Fin m) -> {n : _} -> (f : Fin n) -> Gen MaybeEmpty $ Z f g

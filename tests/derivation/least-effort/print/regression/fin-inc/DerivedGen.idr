module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

record FinInc n where
  constructor MkFinInc
  val : Nat
  prf : LTE val n

%language ElabReflection

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (n ** FinInc n)

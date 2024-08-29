module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

record FinInc n where
  constructor MkFinInc
  val : Nat
  prf : LTE val n

%language ElabReflection

%runElab printDerived @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (n ** FinInc n)

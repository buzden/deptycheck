module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data X : Type where
  E : X
  R : X -> Nat -> X

%runElab printDerived @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X

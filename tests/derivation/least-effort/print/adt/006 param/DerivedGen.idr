module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data X : Nat -> Type where
  MkX : X n

%runElab printDerived @{LeastEffort} $ Fuel -> Gen MaybeEmpty (n ** X n)

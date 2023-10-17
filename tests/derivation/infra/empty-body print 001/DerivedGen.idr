module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

%runElab printDerived {core=EmptyBody} $ Fuel -> Gen MaybeEmpty Unit

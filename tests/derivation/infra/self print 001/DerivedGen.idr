module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

%runElab printDerived {core=CallSelf} $ Fuel -> Gen MaybeEmpty Unit

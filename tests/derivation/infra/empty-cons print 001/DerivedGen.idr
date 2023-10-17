module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

%runElab printDerived {core=EmptyCons} $ Fuel -> Gen MaybeEmpty Unit

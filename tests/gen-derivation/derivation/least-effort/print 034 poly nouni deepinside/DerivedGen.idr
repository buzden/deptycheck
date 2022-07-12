module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data X a = MkX (Maybe (a, a))

%runElab printDerived @{MainCoreDerivator @{LeastEffort}} $ Fuel -> {a : Type} -> (Fuel -> Gen a) => Gen (X a)

module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data X z = MkX (Maybe (z, z))

%runElab printDerived @{MainCoreDerivator @{LeastEffort}} $ Fuel -> {a : Type} -> (Fuel -> Gen a) => Gen (X a)

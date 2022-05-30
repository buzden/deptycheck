module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

%runElab printDerived @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (a, b : Type) -> (Fuel -> Gen a) => (Fuel -> Gen b) => Gen (a, b)

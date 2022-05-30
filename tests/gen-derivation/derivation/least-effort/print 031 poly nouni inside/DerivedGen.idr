module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data X = MkX (Maybe Bool)

%runElab printDerived @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen X

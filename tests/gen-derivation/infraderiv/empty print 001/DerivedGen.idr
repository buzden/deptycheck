module DerivedGen

import AlternativeCore

%default total

%language ElabReflection

%runElab printDerived @{Empty} $ Fuel -> Gen Unit

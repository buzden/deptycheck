module DerivedGen

import AlternativeCore

%default total

%language ElabReflection

%runElab printDerived @{CallSelf} $ Fuel -> Gen Unit

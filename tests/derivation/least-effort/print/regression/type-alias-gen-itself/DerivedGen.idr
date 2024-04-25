module DerivedGen

import AlternativeCore
import PrintDerivation

import Data.Fin

%default total

X : Type
X = Bool

%language ElabReflection

%runElab printDerived @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen0 X

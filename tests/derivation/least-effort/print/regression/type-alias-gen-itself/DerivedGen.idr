module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

X : Type
X = Bool

%language ElabReflection

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen0 X

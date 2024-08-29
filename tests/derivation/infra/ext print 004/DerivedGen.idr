module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{Ext_XSN} $ Fuel -> (Fuel -> Gen MaybeEmpty String) => (n : Nat) -> Gen MaybeEmpty (X'S n)

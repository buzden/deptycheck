module DerivedGen

import Data.List.Sorted

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter $ Fuel -> Gen MaybeEmpty SortedList

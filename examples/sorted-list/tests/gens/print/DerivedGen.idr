module DerivedGen

import PrintDerivation

import Data.List.Sorted

%default total

%language ElabReflection

%runElab printDerived $ Fuel -> Gen MaybeEmpty SortedList

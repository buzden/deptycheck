module DerivedGen

import PrintDerivation

import Data.List.Sorted

%default total

%language ElabReflection

%hint LE : ConstructorDerivator; LE = LeastEffort

%runElab printDerived $ Fuel -> Gen MaybeEmpty SortedList

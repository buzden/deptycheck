module DerivedGen

import Data.List.Sorted

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

%runElab deriveGenPrinter $ Fuel -> Gen MaybeEmpty SortedList

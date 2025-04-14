module DerivedGen

import Data.SortedBinTree

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

%runElab deriveGenPrinter $ Fuel -> Gen MaybeEmpty SortedBinTree

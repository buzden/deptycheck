module Data.SortedBinTree.Gen

import public Data.SortedBinTree

import public Test.DepTyCheck.Gen
import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 5

%hint
UsedConstructorDerivator : ConstructorDerivator
UsedConstructorDerivator = LeastEffort {simplificationHack = True}

export
genSortedBinTrees : Fuel -> Gen MaybeEmpty SortedBinTree
genSortedBinTrees = deriveGen

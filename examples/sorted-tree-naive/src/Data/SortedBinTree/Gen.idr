module Data.SortedBinTree.Gen

import public Data.SortedBinTree

import public Test.DepTyCheck.Gen
import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 5

export
genSortedBinTree : Fuel -> Gen MaybeEmpty SortedBinTree
genSortedBinTree = deriveGen

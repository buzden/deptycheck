module Data.SortedBinTree.Gen

import public Data.SortedBinTree

import public Test.DepTyCheck.Gen
import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 5

export
genSortedBinTree1 : Fuel -> Gen MaybeEmpty (mi ** ma ** SortedBinTree1 mi ma)
genSortedBinTree1 = deriveGen

module Data.List.Sorted.Gen

import public Data.List.Sorted

import public Test.DepTyCheck.Gen
import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 5

%hint
UsedConstructorDerivator : ConstructorDerivator
UsedConstructorDerivator = LeastEffort {simplificationHack = True}

export
genSortedList : Fuel -> Gen MaybeEmpty SortedList
genSortedList = deriveGen

module Data.List.Sorted

import public Data.Nat

%default total

public export
data SortedList : Type

public export
data FirstGT : Nat -> SortedList -> Type

data SortedList : Type where
  Nil  : SortedList
  (::) : (x : Nat) -> (xs : SortedList) -> FirstGT x xs => SortedList

data FirstGT : Nat -> SortedList -> Type where
  E  : FirstGT n []
  NE : x `GT` n -> FirstGT n $ (x::xs) @{prf}

public export
toList : SortedList -> List Nat
toList []      = []
toList (x::xs) = x :: toList xs

module Data.List.Sorted

import public Data.Nat

%default total

public export
data SortedList : Type

namespace SortedList
  public export
  data AllGT : Nat -> SortedList -> Type

data SortedList : Type where
  Nil  : SortedList
  (::) : (x : Nat) -> (xs : SortedList) -> AllGT x xs => SortedList

namespace SortedList
  public export
  data AllGT : Nat -> SortedList -> Type where
    Nil  : AllGT n []
    (::) : AllGT n xs -> x `GT` n -> AllGT n $ (x::xs) @{prf}

public export
toList : SortedList -> List Nat
toList []      = []
toList (x::xs) = x :: toList xs

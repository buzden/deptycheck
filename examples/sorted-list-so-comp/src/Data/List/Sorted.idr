module Data.List.Sorted

import public Data.So

%default total

mutual

  public export
  data SortedList : Type where
    Nil  : SortedList
    (::) : (x : Nat) -> (xs : SortedList) -> LTEHead x xs => SortedList

  public export
  data LTEHead : Nat -> SortedList -> Type where
    NoHead   : LTEHead n []
    SomeHead : So (n < x) -> LTEHead n $ (x::xs) @{_}

public export
length : SortedList -> Nat
length []      = Z
length (_::xs) = S $ length xs

public export
toList : SortedList -> List Nat
toList []      = []
toList (x::xs) = x :: toList xs

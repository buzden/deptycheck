module Data.List.Sorted

import public Data.So

%default total

mutual

  public export
  data SortedList : Type where
    Nil  : SortedList
    (::) : (x : Nat) -> (xs : SortedList) -> (0 _ : So $ canPrepend x xs) => SortedList

  public export
  canPrepend : Nat -> SortedList -> Bool
  canPrepend _ []      = True
  canPrepend n (x::xs) = n < x

public export
length : SortedList -> Nat
length []      = Z
length (_::xs) = S $ length xs

public export
toList : SortedList -> List Nat
toList []      = []
toList (x::xs) = x :: toList xs

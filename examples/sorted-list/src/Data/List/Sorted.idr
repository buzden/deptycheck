module Data.List.Sorted

import public Data.Nat
import public Data.So

%default total

public export
data SortedList : Type

public export
canPrepend : Nat -> SortedList -> Bool

data SortedList : Type where
  Nil  : SortedList
  (::) : (x : Nat) -> (xs : SortedList) -> (0 _ : So $ canPrepend x xs) => SortedList

canPrepend _ []      = True
canPrepend n (x::xs) = x > n

public export
length : SortedList -> Nat
length []      = Z
length (_::xs) = S $ length xs

public export
toList : SortedList -> List Nat
toList []      = []
toList (x::xs) = x :: toList xs

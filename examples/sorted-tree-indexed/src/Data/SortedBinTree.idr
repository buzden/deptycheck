module Data.SortedBinTree

import public Data.Nat

%default total

public export
data SortedBinTree1 : (mi, ma : Nat) -> Type where
  Leaf : (x : Nat) -> SortedBinTree1 x x
  Node : (left : SortedBinTree1 lmi lma) -> (right : SortedBinTree1 rmi rma) -> lma `LT` rmi => SortedBinTree1 lmi rma

export
toList : SortedBinTree1 mi ma -> List Nat
toList (Leaf x)          = [x]
toList (Node left right) = toList left ++ toList right

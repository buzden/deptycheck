module Data.SortedBinTree

import public Data.Nat

%default total

public export
data SortedBinTree1 : (mi, ma : Nat) -> Type where
  Leaf   : (x : Nat) -> SortedBinTree1 x x
  NodeL  : (x : Nat) -> (left : SortedBinTree1 mi ma) -> ma `LT` x => SortedBinTree1 mi x
  NodeR  : (x : Nat) -> (right : SortedBinTree1 mi ma) -> x `LT` mi => SortedBinTree1 x ma
  NodeLR : (x : Nat) -> (left : SortedBinTree1 lmi lma) -> (right : SortedBinTree1 rmi rma) -> x `LT` rmi => lma `LT` x => SortedBinTree1 lmi rma

export
toList : SortedBinTree1 mi ma -> List Nat
toList (Leaf x)              = [x]
toList (NodeL x left)        = toList left ++ [x]
toList (NodeR x right)       = [x] ++ toList right
toList (NodeLR x left right) = toList left ++ [x] ++ toList right

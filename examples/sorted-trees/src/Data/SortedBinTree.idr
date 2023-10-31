module Data.SortedBinTree

import public Data.Nat

%default total

public export
data SortedBinTree : Type

namespace SortedBinTree
  public export
  data All : (Nat -> Type) -> SortedBinTree -> Type

data SortedBinTree : Type where
  Empty : SortedBinTree
  Node  : (x : Nat) -> (left, right : SortedBinTree) -> All (`LT` x) left => All (x `LT`) right => SortedBinTree

namespace SortedBinTree
  data All : (Nat -> Type) -> SortedBinTree -> Type where
    Empty : All prop Empty
    Node  : prop x -> All prop l -> All prop r -> All prop $ Node x l r @{prf1} @{prf2}

public export %inline
Leaf : Nat -> SortedBinTree
Leaf x = Node x Empty Empty

export
toList : SortedBinTree -> List Nat
toList Empty               = []
toList $ Node x left right = toList left ++ [x] ++ toList right

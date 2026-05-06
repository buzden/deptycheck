module Data.SortedBinTree

import public Data.Nat
import Data.Primitives.Interpolation
import Data.String

%default total

public export
data SortedBinTree : Type

namespace SortedBinTree
  public export
  data AllLT : Nat -> SortedBinTree -> Type
  public export
  data AllGT : Nat -> SortedBinTree -> Type

data SortedBinTree : Type where
  Empty : SortedBinTree
  Node  : (x : Nat) -> (left, right : SortedBinTree) -> AllLT x left => AllGT x right => SortedBinTree

namespace SortedBinTree

  data AllLT : Nat -> SortedBinTree -> Type where
    EmptyLT : AllLT ref Empty
    NodeLT  : x `LT` ref -> AllLT ref l -> AllLT ref r -> AllLT ref $ Node x l r @{prf1} @{prf2}

  data AllGT : Nat -> SortedBinTree -> Type where
    EmptyGT : AllGT ref Empty
    NodeGT  : ref `LT` x -> AllGT ref l -> AllGT ref r -> AllGT ref $ Node x l r @{prf1} @{prf2}

public export %inline
Leaf : Nat -> SortedBinTree
Leaf x = Node x Empty Empty

export
toList : SortedBinTree -> List Nat
toList Empty               = []
toList $ Node x left right = toList left ++ [x] ++ toList right

export
Interpolation SortedBinTree where
  interpolate Empty = "*"
  interpolate $ Node x l r = """
    \{show x}
    \{ind "|" $ interpolate l}
    \{ind " " $ interpolate r}
    """
    where
      ind : (pref : String) -> String -> String
      ind k s = do
        let f::fs = lines s | [] => ""
        joinBy "\n" $ "|" :: ("|- " ++ f) :: (("\{k}  " ++) <$> fs)

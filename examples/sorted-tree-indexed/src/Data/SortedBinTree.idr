module Data.SortedBinTree

import public Data.Nat
import Data.String

%default total

public export
data SortedBinTree1 : (mi, ma : Nat) -> Type where
  Leaf : (x : Nat) -> SortedBinTree1 x x
  Node : (left : SortedBinTree1 lmi lma) -> (right : SortedBinTree1 rmi rma) -> lma `LT` rmi => SortedBinTree1 lmi rma

export
toList : SortedBinTree1 mi ma -> List Nat
toList (Leaf x)          = [x]
toList (Node left right) = toList left ++ toList right

export
Interpolation (SortedBinTree1 mi ma) where
  interpolate $ Leaf x = "\{show x}"
  interpolate $ Node l r = """
    .
    \{ind "|" $ interpolate l}
    \{ind " " $ interpolate r}
    """
    where
      ind : (pref : String) -> String -> String
      ind k s = do
        let f::fs = lines s | [] => ""
        joinBy "\n" $ "|" :: ("|- " ++ f) :: (("\{k}  " ++) <$> fs)

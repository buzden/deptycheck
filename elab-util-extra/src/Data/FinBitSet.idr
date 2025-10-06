||| Set of Fin implemented via a bitset
module Data.FinBitSet

import Data.Bits

%default total

public export
record FinBitSet (n : Nat) where
  constructor MkFBS
  inner : Integer

public export
empty : FinBitSet v
empty = MkFBS zeroBits

public export
lookup : Fin v -> FinBitSet v -> Bool
lookup f (MkFBS s) = testBit s $ finToNat f

public export
insert : Fin v -> FinBitSet v -> FinBitSet v
insert f (MkFBS s) = MkFBS $ setBit s $ finToNat f

public export
delete : Fin v -> FinBitSet v -> FinBitSet v
delete f (MkFBS s) = MkFBS $ clearBit s $ finToNat f

public export
fromList : List (Fin v) -> FinBitSet v
fromList = foldl (flip insert) empty

public export
toList : {v : Nat} -> FinBitSet v -> List (Fin v)
toList fbs = filter (flip lookup fbs) $ List.allFins v

public export
removeAll : FinBitSet v -> FinBitSet v -> FinBitSet v
removeAll (MkFBS a) (MkFBS b) = MkFBS $ b .&. (complement a)

public export
merge : FinBitSet v -> FinBitSet v -> FinBitSet v
merge (MkFBS a) (MkFBS b) = MkFBS $ a .|. b

public export
intersection : FinBitSet v -> FinBitSet v -> FinBitSet v
intersection (MkFBS a) (MkFBS b) = MkFBS $ a .&. b

mask' : Integer -> Nat -> Integer
mask' i Z = 0
mask' i x@(S y) = setBit (mask' i y) x

mask : Nat -> Integer
mask = mask' 0

public export
invert : {v : Nat} -> FinBitSet v -> FinBitSet v
invert (MkFBS x) = MkFBS $ complement x .&. mask v

toLN' : Nat -> Integer -> List Nat
toLN' x s = 
  if s == 0 
     then [] 
     else if testBit s 0 
                            -- Since s != 0, shiftR s 1 < s
      then x :: toLN' (S x) (assert_smaller s $ shiftR s 1)
      else toLN' (S x) (assert_smaller s $ shiftR s 1)

toLN : FinBitSet v -> List Nat
toLN (MkFBS s) = toLN' 0 s

public export
Show (FinBitSet v) where
  show fbs = "fromList \{show $ toLN fbs}"

public export
Eq (FinBitSet v) where
  (==) a b = a.inner == b.inner

public export
Semigroup (FinBitSet v) where
  (<+>) = merge

public export
Monoid (FinBitSet v) where
  neutral = empty

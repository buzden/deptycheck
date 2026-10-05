module Deriving.SpecialiseData.QuantifiersExt

import public Data.DPair
import Data.List
import Data.List.Quantifiers
import Data.Vect
import Data.Vect.Quantifiers
import Data.SnocList.Quantifiers

namespace VectAll
  ||| Proof that Vect.All works over Vect.snoc
  export
  0 snoc: All p prev -> p new -> All p (Data.Vect.snoc prev new)
  snoc [] y = [y]
  snoc (y :: ys) z = y :: snoc ys z

  ||| List + List.All to Vect + Vect.All
  export
  fromListAll : (l : List t) -> (0 pr : All p l) => Subset (Vect (length l) t) (All p)
  fromListAll [] = Element [] []
  fromListAll (x :: xs) @{p :: ps} = do
    let Element xs' ps' = fromListAll xs @{ps}
    Element (x :: xs') (p :: ps')

namespace ListAll
  ||| Proof that List.All works over List.snoc
  export
  0 snoc : All p prev -> p new -> All p (Data.List.snoc prev new)
  snoc [] y = [y]
  snoc (y :: ys) z = y :: snoc ys z

namespace SnocListAll
  ||| SnocList + SnocList.All to List + List.All
  export
  toListAll : (sl : SnocList t) -> (0 _ : All p sl) -> Subset (List t) (All p)
  toListAll [<] [<] = Element [] []
  toListAll (sx :< x) (sy :< y) = do
    let Element xs ys = toListAll sx sy
    Element (snoc xs x) (snoc ys y)


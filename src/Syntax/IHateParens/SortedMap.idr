module Syntax.IHateParens.SortedMap

import public Data.SortedMap
import Data.Vect

import Syntax.IHateParens.List

%default total

public export %inline
(.asList) : SortedMap k v -> List (k, v)
m.asList = SortedMap.toList m

public export %inline
(.size) : SortedMap k v -> Nat
m.size = m.asList.length

public export %inline
(.asVect) : (m : SortedMap k v) -> Vect m.size (k, v)
s.asVect = fromList s.asList

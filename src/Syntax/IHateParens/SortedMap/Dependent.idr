module Syntax.IHateParens.SortedMap.Dependent

import public Data.SortedMap.Dependent
import Data.Vect

import Syntax.IHateParens.List

%default total

public export %inline
(.asList) : SortedDMap k v -> List (x : k ** v x)
m.asList = toList m

public export %inline
(.size) : SortedDMap k v -> Nat
m.size = m.asList.length

public export %inline
(.asVect) : (m : SortedDMap k v) -> Vect m.size (x : k ** v x)
s.asVect = fromList s.asList

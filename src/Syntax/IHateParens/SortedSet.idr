module Syntax.IHateParens.SortedSet

import public Data.SortedSet
import Data.Vect

import Syntax.IHateParens.List

%default total

public export %inline
(.asList) : SortedSet a -> List a
s.asList = SortedSet.toList s

public export %inline
(.size) : SortedSet a -> Nat
m.size = m.asList.length

public export %inline
(.asVect) : (s : SortedSet a) -> Vect s.size a
s.asVect = fromList s.asList

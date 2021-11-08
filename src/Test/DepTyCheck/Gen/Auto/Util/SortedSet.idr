module Test.DepTyCheck.Gen.Auto.Util.SortedSet

import public Data.List

import public Data.SortedMap
import public Data.SortedMap.Dependent
import public Data.SortedSet

%default total

-----------------------------
--- `SortedSet` utilities ---
-----------------------------

-- Not really a functor's `map`, because map fusion law does not hold
export
mapIn : Ord b => (a -> b) -> SortedSet a -> SortedSet b
mapIn f = fromList . map f . SortedSet.toList

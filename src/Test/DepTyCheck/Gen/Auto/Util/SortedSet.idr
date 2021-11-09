module Test.DepTyCheck.Gen.Auto.Util.SortedSet

import public Data.List
import public Data.List1

import public Data.SortedMap
import public Data.SortedMap.Dependent
import public Data.SortedSet

import public Test.DepTyCheck.Gen.Auto.Util.Syntax

%default total

-----------------------------
--- `SortedSet` utilities ---
-----------------------------

-- Not really a functor's `map`, because map fusion law does not hold
export
mapIn : Ord b => (a -> b) -> SortedSet a -> SortedSet b
mapIn f = fromList . map f . SortedSet.toList

export
fromFoldable : Ord a => Foldable f => f a -> SortedSet a
fromFoldable = foldl (flip insert) empty

export
allPermutations : Ord a => SortedSet a -> List1 $ List a
allPermutations s = case fromList s.asList of
  Nothing => pure []
  Just ss => do
    e  <- ss
    es <- allPermutations $ assert_smaller s $ delete e s
    pure $ e :: es

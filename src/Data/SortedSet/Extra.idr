module Data.SortedSet.Extra

import Data.SortedSet

%default total

-- Not really a functor's `map`, because map fusion law does not hold
export
mapIn : Ord b => (a -> b) -> SortedSet a -> SortedSet b
mapIn f = fromList . map f . SortedSet.toList

export
mapInMaybe : Ord b => (a -> Maybe b) -> SortedSet a -> SortedSet b
mapInMaybe f = fromList . mapMaybe f . SortedSet.toList

export
fromFoldable : Ord a => Foldable f => f a -> SortedSet a
fromFoldable = foldl insert' empty

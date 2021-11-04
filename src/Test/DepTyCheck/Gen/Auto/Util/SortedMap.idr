module Test.DepTyCheck.Gen.Auto.Util.SortedMap

import public Data.List

import public Data.SortedMap
import public Data.SortedMap.Dependent

import public Test.DepTyCheck.Gen.Auto.Util.Syntax

%default total

-----------------------------
--- `SortedMap` utilities ---
-----------------------------

export
mapMaybe : Ord k => (a -> Maybe b) -> SortedMap k a -> SortedMap k b
mapMaybe f = SortedMap.fromList . mapMaybe (\(k, a) => (k,) <$> f a) . SortedMap.toList

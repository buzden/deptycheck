module Data.SortedMap.Extra

import Data.List
import Data.SortedMap

import Syntax.IHateParens

%default total

export
mapMaybe : Ord k => (a -> Maybe b) -> SortedMap k a -> SortedMap k b
mapMaybe f = SortedMap.fromList . mapMaybe (\(k, a) => (k,) <$> f a) . SortedMap.toList

----------------------------------------------------------
--- Properties of collections (most actually unproved) ---
----------------------------------------------------------

export
mapAsList : (f : v -> w) -> (m : SortedMap k v) -> (map f m).asList === map (mapSnd f) m.asList
mapAsList f m = believe_me $ Refl {x=Z}

export
mapSize : (f : v -> w) -> (m : SortedMap k v) -> (map f m).size = m.size
mapSize f m = rewrite mapAsList f m in lengthMap _

export
keySetSize : (m : SortedMap k v) -> (keySet m).size = m.size
keySetSize m = believe_me $ Refl {x=Z}

export
keysThruAsList : (m : SortedMap k v) -> keys m === (Builtin.fst <$> m.asList)
keysThruAsList m = believe_me $ Refl {x=Z}

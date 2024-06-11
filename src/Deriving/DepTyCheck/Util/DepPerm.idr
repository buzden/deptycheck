-- This module exists only to put out couple of heavily copiling functions, to speed up compilation time
module Deriving.DepTyCheck.Util.DepPerm

import public Data.Fin.ToFin
import public Data.Vect.Dependent
import public Data.SortedMap
import public Data.SortedMap.Dependent
import public Data.SortedSet

import public Deriving.DepTyCheck.Util.Collections

export
disjointDepSets : (rawDeps : DVect n $ SortedSet . Fin . Fin.finToNat) -> (givs : SortedSet $ Fin n) -> List $ SortedSet $ Fin n
disjointDepSets rawDeps givs = do

  -- For each argument calculate the minimal index of its dependency (itself, if no dependencies)
  let minDeps : DVect n (Fin . S . finToNat) :=
       flip mapPreI rawDeps $ \i, pre =>
         concatMap @{Minimum} (\j => weakenToSuper {i=FS j} $ rewrite sym $ weakenToSuper_correct {i} j in index j pre) .
           (`difference` mapInMaybe tryToFit givs)

  -- Get rid of dependent vector, weaken indices bounds
  let minDeps = downmap (weakenToSuper {i=FS _}) minDeps

  -- Reverse the map, i.e. for each minimal index get the set of arguments that depend on it
  let minDeps : SortedMap (Fin $ S $ n) (SortedSet $ Fin n) :=
    concatMap (uncurry SortedMap.singleton) $ map (mapSnd SortedSet.singleton) $ toListI $ minDeps

  -- Acquire a list of disjoint sets, which in each set all args dependent somehow, but args from different susets are independent
  Prelude.toList minDeps

export
indepPermutations : (independencyGroups : List $ SortedSet $ Fin n) -> SortedSet (Fin n) -> List1 $ List $ Fin n
indepPermutations groups s = map concat $ for groups $ allPermutations . intersection s

public export %inline
indepPermutations' : (independencyGroups : List $ SortedSet $ Fin n) -> SortedSet (Fin n) -> List $ List $ Fin n
indepPermutations' = forget .: indepPermutations

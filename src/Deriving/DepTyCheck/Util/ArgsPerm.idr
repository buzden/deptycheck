module Deriving.DepTyCheck.Util.ArgsPerm

import public Data.List.Ex
import public Data.SortedMap
import public Data.Vect

import public Decidable.Equality

import public Language.Reflection
import public Language.Reflection.Syntax
import public Language.Reflection.Syntax.Ops

import public Syntax.IHateParens.List
import public Syntax.IHateParens.Vect

%default total

--------------------------------
--- Permutation of arguments ---
--------------------------------

export
orderIndices : Ord a => (xs : List a) -> Vect xs.length $ Fin xs.length
orderIndices [] = []
orderIndices xs@(_::_) = do
  let idxMap = SortedMap.fromList $ mapI (sort xs) $ flip $ rewrite sortedPreservesLength xs in (,)
  fromMaybe FZ . lookup' idxMap <$> xs.asVect
  --        ^^ - must never happen, if `Ord` is an order mathematically
  where
    sortedPreservesLength : (xs : List a) -> length (sort xs) = xs.length
    sortedPreservesLength xs = believe_me $ Refl {x=Z} -- in the sake of honesty, we need to prove this

export
reorder : (perm : Vect n $ Fin n) -> Vect n a -> Vect n a
reorder perm orig = perm <&> flip index orig

export
reorder' : (xs : List a) -> (perm : Vect xs.length $ Fin xs.length) -> (ys : List a ** ys.length = xs.length)
reorder' orig perm = do
  let xs = reorder perm orig.asVect
  (toList xs ** toListLength xs)
  where
    toList : Vect n a -> List a
    toList []      = []
    toList (x::xs) = x :: toList xs

    toListLength : (xs : Vect n a) -> length (toList xs) = n
    toListLength []      = Refl
    toListLength (x::xs) = rewrite toListLength xs in Refl

export
reorder'' : Maybe (n ** Vect n $ Fin n) -> List TTImp -> Maybe $ List TTImp
reorder'' Nothing xs = pure xs
reorder'' (Just (n ** perm)) xs = do
  let Yes prf = decEq (length xs) n | No _ => Nothing
  Just $ fst $ reorder' xs $ rewrite prf in perm

||| Produces expression returning a mkdpair in a different order, if needed
|||
||| Direct means that given expression which returns acending order, result is permutated; non-direct means vice versa.
export
reorderGend : (direct : Bool) -> {n : _} -> (perm : Vect n $ Fin n) -> TTImp -> TTImp
reorderGend direct perm e = do
  let perm = toList perm
  let all = allFins _
  let False = perm == all | True => e
  let (lhs, rhs) : (_, _) := if direct then (all, perm) else (perm, all)
  let lhs = simpleMkdpair True lhs
  let rhs = simpleMkdpair False rhs
  let lamName : Name := "^lam_arg^"
  `(Prelude.(<&>)) .$ e .$ lam (lambdaArg lamName) (iCase (var lamName) implicitFalse $ pure $ patClause lhs rhs)
  where
    v : (bind : Bool) -> Name -> TTImp
    v bind = if bind then bindVar else var
    simpleMkdpair : (bind : Bool) -> List (Fin n) -> TTImp
    simpleMkdpair bind = foldr (app . (app `(Builtin.DPair.MkDPair)) . v bind . UN . Basic . ("^a" ++) . show) (v bind "^res^")

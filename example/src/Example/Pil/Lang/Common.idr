module Example.Pil.Lang.Common

import public Data.Vect

import Decidable.Decidable
import Decidable.Equality

%default total

namespace Types

  --- Available types in the system ---

  public export
  data Type' = Bool' | Int' | String'

  public export
  idrTypeOf : Type' -> Type
  idrTypeOf Bool'   = Bool
  idrTypeOf Int'    = Int
  idrTypeOf String' = String

  public export
  DecEq Type' where
    decEq Bool'   Bool'   = Yes Refl
    decEq Int'    Int'    = Yes Refl
    decEq String' String' = Yes Refl

    decEq Bool'   Int'    = No \case Refl impossible
    decEq Bool'   String' = No \case Refl impossible

    decEq Int'    Bool'   = No \case Refl impossible
    decEq Int'    String' = No \case Refl impossible

    decEq String' Bool'   = No \case Refl impossible
    decEq String' Int'    = No \case Refl impossible

namespace Auxiliary

  --- Auxiliary data definitions and their instances ---

  export
  data Name = MkName String

  %name Name n, m

  export
  FromString Name where
    fromString = MkName

  export
  Eq Name where
    MkName n == MkName m = n == m

  export
  Show Name where
    show (MkName n) = n

  export
  DecEq Name where
    decEq (MkName n) (MkName m) = case decEq n m of
      Yes Refl => Yes Refl
      No co => No \case Refl => co Refl

namespace Invariant

  --- Static context in terms of which we are formulating an invariant ---

  namespace Variable

    public export
    Variables : Type
    Variables = List (Name, Type')

    %name Variables vars

  namespace Register

    public export
    data Registers : Nat -> Type where
      Base  : Vect rc $ Maybe Type' -> Registers rc
      Merge : Registers rc -> Registers rc -> Registers rc
      With  : Registers rc -> (Fin rc, Maybe Type') -> Registers rc

    %name Registers regs

    public export
    DecEq (Registers rc) where

      decEq (Base xs) (Base ys) = case (decEq xs ys) of
        Yes Refl => Yes Refl
        No up => No $ up . \case Refl => Refl

      decEq (Merge r1 r2) (Merge s1 s2) = case (decEq r1 s1, decEq r2 s2) of
        (Yes Refl, Yes Refl) => Yes Refl
        (_, No us) => No $ us . \case Refl => Refl
        (No up, _) => No $ up . \case Refl => Refl

      decEq (With rs1 (r1, ty1)) (With rs2 (r2, ty2)) = case (decEq rs1 rs2, decEq r1 r2, decEq ty1 ty2) of
        (Yes Refl, Yes Refl, Yes Refl) => Yes Refl
        (_, _, No ur) => No $ ur . \case Refl => Refl
        (_, No uq, _) => No $ uq . \case Refl => Refl
        (No up, _, _) => No $ up . \case Refl => Refl

      decEq (Base _)    (Merge _ _) = No \case Refl impossible
      decEq (Base _)    (With _ _)  = No \case Refl impossible
      decEq (Merge _ _) (Base _)    = No \case Refl impossible
      decEq (Merge _ _) (With _ _)  = No \case Refl impossible
      decEq (With _ _)  (Base _)    = No \case Refl impossible
      decEq (With _ _)  (Merge _ _) = No \case Refl impossible

    public export
    AllUndefined : {rc : Nat} -> Registers rc
    AllUndefined = Base $ replicate rc Nothing

    --- Rules of merging of independent register types ---

    public export
    mergeSame : Maybe Type' -> Maybe Type' -> Maybe Type'
    mergeSame Nothing  _        = Nothing
    mergeSame (Just _) Nothing  = Nothing
    mergeSame (Just x) (Just y) = case decEq x y of
      Yes _ => Just x
      No  _ => Nothing

    namespace MergeSameProperties

      export
      mergeSame_idempotent : (x : _) -> mergeSame x x = x
      mergeSame_idempotent Nothing = Refl
      mergeSame_idempotent (Just x) = rewrite decEqSelfIsYes {x} in Refl

      export
      mergeSame_commutative : (x, y : _) -> mergeSame x y = mergeSame y x
      mergeSame_commutative Nothing  Nothing  = Refl
      mergeSame_commutative Nothing  (Just _) = Refl
      mergeSame_commutative (Just _) Nothing  = Refl
      mergeSame_commutative (Just x) (Just y) with (decEq x y)
        mergeSame_commutative (Just x) (Just x) | Yes Refl = rewrite decEqSelfIsYes {x} in Refl
        mergeSame_commutative (Just x) (Just y) | No uxy with (decEq y x)
          mergeSame_commutative (Just _) (Just _) | No _   | No  _  = Refl
          mergeSame_commutative (Just _) (Just _) | No uxy | Yes yx = absurd $ uxy $ sym yx

      export
      mergeSame_nothing_absorbs_r : (x : _) -> mergeSame x Nothing = Nothing
      mergeSame_nothing_absorbs_r Nothing  = Refl
      mergeSame_nothing_absorbs_r (Just _) = Refl

      export
      mergeSame_associative : (x, y, z : _) -> (x `mergeSame` y) `mergeSame` z = x `mergeSame` (y `mergeSame` z)
      mergeSame_associative Nothing  _        _        = Refl
      mergeSame_associative (Just x) Nothing  _        = Refl
      mergeSame_associative (Just x) (Just y) Nothing  = mergeSame_nothing_absorbs_r _
      mergeSame_associative (Just x) (Just y) (Just z) with (decEq x y)
        mergeSame_associative (Just y) (Just y) (Just z) | Yes Refl with (decEq y z)
          mergeSame_associative (Just _) (Just _) (Just z) | Yes Refl | Yes Refl = rewrite decEqSelfIsYes {x=z} in Refl
          mergeSame_associative (Just _) (Just _) (Just _) | Yes Refl | No _     = Refl
        mergeSame_associative (Just x) (Just y) (Just z) | No uxy with (decEq y z)
          mergeSame_associative (Just x) (Just y) (Just z) | No uxy | Yes _  = rewrite snd $ decEqContraIsNo uxy in Refl
          mergeSame_associative (Just x) (Just y) (Just z) | No uxy | No uyz = Refl

    --- Eliminators for the `Registers` type ---

    public export
    index : Fin rc -> Registers rc -> Maybe Type'
    index i $ Base xs         = Vect.index i xs
    index i $ Merge r1 r2     = mergeSame (index i r1) (index i r2)
    index i $ With rs (n, ty) = if isYes $ decEq i n then ty else index i rs

    public export
    squash : Registers rc -> Vect rc $ Maybe Type'
    squash $ Base xs = xs
    squash $ Merge r1 r2 = zipWith mergeSame (squash r1) (squash r2)
    squash $ With rs (n, ty) = replaceAt n ty $ squash rs

    export
    squash_preserves_index : (i : Fin rc) -> (regs : Registers rc) -> index i (squash regs) = index i regs
    squash_preserves_index _ $ Base _ = Refl
    squash_preserves_index i $ Merge r1 r2 = rewrite zipWithIndexLinear mergeSame (squash r1) (squash r2) i in
                                             rewrite squash_preserves_index i r1 in
                                             rewrite squash_preserves_index i r2 in
                                             Refl
    squash_preserves_index i $ With rs (n, ty) with (decEq i n)
      squash_preserves_index i $ With rs (i, ty) | Yes Refl = replaceAtSameIndex _ _ _
      squash_preserves_index i $ With rs (n, ty) | No co = rewrite replaceAtDiffIndexPreserves (squash rs) i n co ty in
                                                           squash_preserves_index i rs

    --- Showing the registers state as a string ---

    Show (Maybe Type') where
      show $ Just Bool'   = "Bool"
      show $ Just Int'    = "Int"
      show $ Just String' = "String"
      show $ Nothing      = "-"

    export
    Show (Registers rc) where
      show = show . squash

    --- Index-equivalence relation ---

    infix 0 =%=

    -- Extensional equality regarding to the `index` function for any possible indexing argument.
    public export
    data (=%=) : Registers rc -> Registers rc -> Type where
      EquivByIndex : {0 l, r : Registers rc} -> ((i : Fin rc) -> index i l = index i r) -> l =%= r

    public export %inline
    (.ieq) : x =%= y -> (i : _) -> index i x = index i y
    (.ieq) (EquivByIndex f) = f

    export %hint
    index_equiv_refl : x =%= x
    index_equiv_refl = EquivByIndex \_ => Refl

    export %hint
    index_equiv_sym : x =%= y -> y =%= x
    index_equiv_sym xy = EquivByIndex \i => sym $ xy.ieq i

    export %hint
    index_equiv_trans : x =%= y -> y =%= z -> x =%= z
    index_equiv_trans xy yz = EquivByIndex \i => trans (xy.ieq i) (yz.ieq i)

    --- Equivalence properties of `Merge` ---

    export %hint
    merge_commutative : {l, r : _} -> Merge l r =%= Merge r l
    merge_commutative = EquivByIndex \i => mergeSame_commutative _ _

    export %hint
    merge_associative : {a, b, c : _} -> (a `Merge` b) `Merge` c =%= a `Merge` (b `Merge` c)
    merge_associative = EquivByIndex \i => mergeSame_associative _ _ _

    export %hint
    merge_idempotent : {x : _} -> Merge x x =%= x
    merge_idempotent = EquivByIndex \i => mergeSame_idempotent _

    --- Equivalence properties of `With` ---

    export %hint
    withed_with_same_equiv : {x : _} -> {j : _} -> x `With` (j, index j x) =%= x
    withed_with_same_equiv = EquivByIndex \i => case decEq i j of
                               Yes Refl => rewrite decEqSelfIsYes {x=j} in Refl
                               No co => rewrite snd $ decEqContraIsNo co in Refl

    --- Equivalence properties of `squash` ---

    export %hint
    squashed_regs_equiv : {x : _} -> Base (squash x) =%= x
    squashed_regs_equiv = EquivByIndex \i => squash_preserves_index i x

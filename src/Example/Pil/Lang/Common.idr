module Example.Pil.Lang.Common

import public Data.Vect

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

  export
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

    %name Registers regs

    public export
    AllUndefined : {rc : Nat} -> Registers rc
    AllUndefined = Base $ replicate rc Nothing

    public export
    mergeSame : Maybe Type' -> Maybe Type' -> Maybe Type'
    mergeSame Nothing  Nothing  = Nothing
    mergeSame Nothing  (Just _) = Nothing
    mergeSame (Just _) Nothing  = Nothing
    mergeSame (Just x) (Just y) = case decEq x y of
      Yes _ => Just x
      No  _ => Nothing

    public export
    index : Fin rc -> Registers rc -> Maybe Type'
    index i $ Base xs     = Vect.index i xs
    index i $ Merge r1 r2 = mergeSame (index i r1) (index i r2)

    --- Index-equivalence relation ---

    infix 0 =%=

    -- Extensional equality regarding to the `index` function for any possible indexing argument.
    public export
    data (=%=) : Registers rc -> Registers rc -> Type where
      EquivByIndex : ((i : Fin rc) -> index i l = index i r) -> l =%= r

    export %hint
    index_equiv_refl : {0 x : Registers rc} -> x =%= x
    index_equiv_refl = EquivByIndex {rc} \_ => Refl

    export %hint
    index_equiv_sym : {0 x, y : Registers rc} -> x =%= y -> y =%= x
    index_equiv_sym (EquivByIndex xy) = EquivByIndex \i => sym $ xy i

    export %hint
    index_equiv_trans : {x, y, z : _} -> x =%= y -> y =%= z -> x =%= z

    --- Equivalence properties of `Merge` ---

    export %hint
    merge_commutative : {l, r : _} -> Merge l r =%= Merge r l

    export %hint
    merge_associative : {a, b, c : _} -> (a `Merge` b) `Merge` c =%= a `Merge` (b `Merge` c)

    export %hint
    merge_refl : {x : _} -> Merge x x =%= x

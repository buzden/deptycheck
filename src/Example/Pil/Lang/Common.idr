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
    data RegisterTyUpdate = NoTypeUpdate | SetTo Type' | SetUndefined

    public export
    RegisterTyUpdates : Nat -> Type
    RegisterTyUpdates rc = Vect rc RegisterTyUpdate

    %name RegisterTyUpdates upds

    public export
    NoTyUpdates : {rc : Nat} -> RegisterTyUpdates rc
    NoTyUpdates = replicate rc NoTypeUpdate

    public export
    data Registers : Nat -> Type where
      Base   : Vect rc $ Maybe Type' -> Registers rc
      Update : Registers rc -> RegisterTyUpdates rc -> Registers rc
      Merge  : Registers rc -> RegisterTyUpdates rc -> RegisterTyUpdates rc -> Registers rc

    %name Registers regs

    public export
    AllUndefined : {rc : Nat} -> Registers rc
    AllUndefined = Base $ replicate rc Nothing

    public export
    updatedRegisterType : Maybe Type' -> RegisterTyUpdate -> Maybe Type'
    updatedRegisterType ty NoTypeUpdate = ty
    updatedRegisterType _  (SetTo nty)  = Just nty
    updatedRegisterType _  SetUndefined = Nothing

    public export
    mergeSame : Type' -> Type' -> Maybe Type'
    mergeSame x y = case decEq x y of
      Yes _ => Just x
      No  _ => Nothing

    public export
    mergeSame' : Maybe Type' -> Type' -> Maybe Type'
    mergeSame' m y = m >>= mergeSame y

    public export
    threeWayMergeUpd : Maybe Type' -> RegisterTyUpdate -> RegisterTyUpdate -> Maybe Type'
    threeWayMergeUpd _  SetUndefined _            = Nothing
    threeWayMergeUpd _  NoTypeUpdate SetUndefined = Nothing
    threeWayMergeUpd _  (SetTo _)    SetUndefined = Nothing
    threeWayMergeUpd ty NoTypeUpdate NoTypeUpdate = ty
    threeWayMergeUpd ty NoTypeUpdate (SetTo y)    = mergeSame' ty y
    threeWayMergeUpd ty (SetTo x)    NoTypeUpdate = mergeSame' ty x
    threeWayMergeUpd _  (SetTo x)    (SetTo y)    = mergeSame x y

    export
    threeWayMergeUpd_commutative : (ty : Maybe Type') -> (u1, u2 : RegisterTyUpdate) -> threeWayMergeUpd ty u1 u2 = threeWayMergeUpd ty u2 u1

    public export
    index : Fin rc -> Registers rc -> Maybe Type'
    index i $ Base xs          = Vect.index i xs
    index i $ Update regs upd  = updatedRegisterType (index i regs) (index i upd)
    index i $ Merge regs u1 u2 = threeWayMergeUpd (index i regs) (index i u1) (index i u2)

    export
    index_update_neutral : (i : _) -> (regs : _) -> index i regs = index i (Update regs NoTyUpdates)

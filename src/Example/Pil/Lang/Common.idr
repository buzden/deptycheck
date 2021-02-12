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
    Registers : Nat -> Type
    Registers n = Vect n $ Maybe Type'

    %name Registers regs

    public export
    AllUndefined : {rc : Nat} -> Registers rc
    AllUndefined = replicate rc Nothing

    namespace Updates

      public export
      data RegisterTyUpdate = NoTypeUpdate | SetTo Type' | SetUndefined

      public export
      RegisterTyUpdates : Nat -> Type
      RegisterTyUpdates rc = Vect rc RegisterTyUpdate

      public export
      NoTyUpdates : {rc : Nat} -> RegisterTyUpdates rc
      NoTyUpdates = replicate rc NoTypeUpdate

      --- Update of a state with updates ---

      public export
      updateRegisterType : Maybe Type' -> RegisterTyUpdate -> Maybe Type'
      updateRegisterType ty NoTypeUpdate = ty
      updateRegisterType _  (SetTo nty)  = Just nty
      updateRegisterType _  SetUndefined = Nothing

      public export
      withUpdates : Registers rc -> RegisterTyUpdates rc -> Registers rc
      withUpdates = zipWith updateRegisterType

      export
      withUpdates_neutral : (regs : Registers rc) -> regs `withUpdates` NoTyUpdates = regs
      withUpdates_neutral []      = Refl
      withUpdates_neutral (_::rs) = rewrite withUpdates_neutral rs in Refl

      --- Merge of independent updates ---

      public export
      theOnly : Type' -> Type' -> Maybe Type'
      theOnly x y = case decEq x y of
        Yes p => Just x
        No up => Nothing

      public export
      whenSame : Maybe Type' -> Type' -> Maybe Type'
      whenSame (Just x) y = theOnly x y
      whenSame Nothing  _ = Nothing

      public export
      threeWayMergeUpd : Maybe Type' -> RegisterTyUpdate -> RegisterTyUpdate -> Maybe Type'
      threeWayMergeUpd ty SetUndefined _            = Nothing
      threeWayMergeUpd ty NoTypeUpdate NoTypeUpdate = ty
      threeWayMergeUpd ty NoTypeUpdate SetUndefined = Nothing
      threeWayMergeUpd ty NoTypeUpdate (SetTo y)    = whenSame ty y
      threeWayMergeUpd ty (SetTo x)    NoTypeUpdate = whenSame ty x
      threeWayMergeUpd ty (SetTo _)    SetUndefined = Nothing
      threeWayMergeUpd ty (SetTo x)    (SetTo y)    = theOnly x y

      export
      threeWayMergeUpd_commutative : (ty : Maybe Type') -> (u1, u2 : RegisterTyUpdate) -> threeWayMergeUpd ty u1 u2 = threeWayMergeUpd ty u2 u1

      public export
      threeWayMergeUpds : Registers rc -> RegisterTyUpdates rc -> RegisterTyUpdates rc -> Registers rc
      threeWayMergeUpds = zipWith3 threeWayMergeUpd

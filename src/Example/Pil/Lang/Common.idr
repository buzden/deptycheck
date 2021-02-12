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
      noUpdateWhenSame : Maybe Type' -> Type' -> RegisterTyUpdate
      noUpdateWhenSame Nothing  _ = SetUndefined
      noUpdateWhenSame (Just x) y = case decEq x y of
                                      Yes p => NoTypeUpdate
                                      No up => SetUndefined

      public export
      threeWayMergeUpd : Maybe Type' -> RegisterTyUpdate -> RegisterTyUpdate -> RegisterTyUpdate
      threeWayMergeUpd _  SetUndefined _            = SetUndefined
      threeWayMergeUpd _  NoTypeUpdate SetUndefined = SetUndefined
      threeWayMergeUpd _  NoTypeUpdate NoTypeUpdate = NoTypeUpdate
      threeWayMergeUpd ty NoTypeUpdate (SetTo y)    = noUpdateWhenSame ty y
      threeWayMergeUpd ty (SetTo x)    NoTypeUpdate = noUpdateWhenSame ty x
      threeWayMergeUpd _  (SetTo _)    SetUndefined = SetUndefined
      threeWayMergeUpd _  (SetTo x)    (SetTo y)    = case decEq x y of
                                                        Yes p => SetTo x
                                                        No up => SetUndefined

      export
      threeWayMergeUpd_commutative : (ty : Maybe Type') -> (u1, u2 : RegisterTyUpdate) -> threeWayMergeUpd ty u1 u2 = threeWayMergeUpd ty u2 u1

      export
      threeWayMergeUpd_associative : (ty : Maybe Type') -> (u1, u2, u3 : RegisterTyUpdate) ->
                                     let op = threeWayMergeUpd ty in (u1 `op` u2) `op` u3 = u1 `op` (u2 `op` u3)

      public export
      threeWayMergeUpds : Registers rc -> RegisterTyUpdates rc -> RegisterTyUpdates rc -> RegisterTyUpdates rc
      threeWayMergeUpds = zipWith3 threeWayMergeUpd

||| This module contains copies of the pre-overhaul definitions of the `elab-util` library and/or code derived from these copies
||| (the overhaul is this one: https://github.com/stefan-hoeck/idris2-elab-util/pull/56).
||| This is done due to be able to migrate to the newer `elab-util` slowly, using both old and new definitions.
|||
||| This copying is done with the permission of Stefan Höck, the author and copyright holder of the `elab-util` library.
module Language.Reflection.Compat

import public Data.List.Quantifiers
import public Data.List1
import public Data.String
import public Data.Vect

import public Language.Reflection
import public Language.Reflection.Syntax
import public Language.Reflection.Syntax.Ops

%default total

public export
stname : Maybe Name -> Name
stname = fromMaybe $ UN Underscore

public export
argName : Arg -> Name
argName = stname . (.name)

cleanupNamedHoles : TTImp -> TTImp
cleanupNamedHoles = mapTTImp $ \case
  IHole {} => implicitFalse
  e        => e

--------------------------------------------------------------------------------
--          General Types
--------------------------------------------------------------------------------

||| Constructor of a data type
public export
record Con where
  constructor MkCon
  name : Name
  args : List Arg
  type : TTImp

||| Tries to lookup a constructor by name.
export
getCon : Elaboration m => Name -> m Con
getCon n = do (n', tt) <- lookupName n
              let (args, tpe) = unPi $ cleanupNamedHoles tt
              pure $ MkCon n' args tpe

||| Information about a data type
|||
||| @name : Name of the data type
|||         Note: There is no guarantee that the name will be fully
|||         qualified
||| @args : Type arguments of the data type
||| @cons : List of data constructors
public export
record TypeInfo where
  constructor MkTypeInfo
  name : Name
  args : List Arg
  cons : List Con

||| Tries to get information about the data type specified
||| by name. The name need not be fully qualified, but
||| needs to be unambiguous.
export
getInfo' : Elaboration m => Name -> m TypeInfo
getInfo' n = do
  (n',tt)        <- lookupName n
  let (args,IType _) = unPi $ cleanupNamedHoles tt
    | (_,_) => fail "Type declaration does not end in IType"
  conNames       <- getCons n'
  cons           <- traverse getCon conNames
  pure (MkTypeInfo n' args cons)

||| macro version of `getInfo'`
export %macro
getInfo : Name -> Elab TypeInfo
getInfo = getInfo'

--- Namedness property ---

public export
data IsNamedArg : Arg -> Type where
  ItIsNamed : IsNamedArg $ MkArg cnt pii (Just n) ty

public export
isNamedArg : (arg : Arg) -> Dec $ IsNamedArg arg
isNamedArg (MkArg count piInfo (Just x) type) = Yes ItIsNamed
isNamedArg (MkArg count piInfo Nothing type)  = No $ \case ItIsNamed impossible

public export
data ConArgsNamed : Con -> Type where
  TheyAreNamed : All IsNamedArg ars -> ConArgsNamed $ MkCon nm ars ty

public export
areConArgsNamed : (con : Con) -> Dec $ ConArgsNamed con
areConArgsNamed $ MkCon _ ars _ with (all isNamedArg ars)
  _ | Yes ars' = Yes $ TheyAreNamed ars'
  _ | No nars  = No $ \(TheyAreNamed ars') => nars ars'

public export
data AllTyArgsNamed : TypeInfo -> Type where
  TheyAllAreNamed : All IsNamedArg ars -> All ConArgsNamed cns -> AllTyArgsNamed $ MkTypeInfo nm ars cns

public export
areAllTyArgsNamed : (ty : TypeInfo) -> Dec $ AllTyArgsNamed ty
areAllTyArgsNamed $ MkTypeInfo _ ars cns with (all isNamedArg ars, all areConArgsNamed cns)
  _ | (Yes ars', Yes cns') = Yes $ TheyAllAreNamed ars' cns'
  _ | (No nars, _) = No $ \(TheyAllAreNamed ars' _) => nars ars'
  _ | (_, No ncns) = No $ \(TheyAllAreNamed _ cns') => ncns cns'

-------------------------------------
--- Working around type inference ---
-------------------------------------

public export %inline
(.tyArgs) : TypeInfo -> List Arg
(.tyArgs) = args

public export %inline
(.tyCons) : TypeInfo -> List Con
(.tyCons) = cons

public export %inline
(.conArgs) : Con -> List Arg
(.conArgs) = args

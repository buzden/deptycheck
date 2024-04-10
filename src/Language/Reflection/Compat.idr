||| This module contains copies of the pre-overhaul definitions of the `elab-util` library and/or code derived from these copies
||| (the overhaul is this one: https://github.com/stefan-hoeck/idris2-elab-util/pull/56).
||| This is done due to be able to migrate to the newer `elab-util` slowly, using both old and new definitions.
|||
||| This copying is done with the permission of Stefan Höck, the author and copyright holder of the `elab-util` library.
module Language.Reflection.Compat

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
              let (args, tpe) = unPi tt
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
  let (args,IType _) = unPi tt
    | (_,_) => fail "Type declaration does not end in IType"
  conNames       <- getCons n'
  cons           <- traverse getCon conNames
  pure (MkTypeInfo n' args cons)

||| macro version of `getInfo'`
export %macro
getInfo : Name -> Elab TypeInfo
getInfo = getInfo'

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

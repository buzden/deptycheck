||| `Language.Reflection`-related utilities
module Test.DepTyCheck.Gen.Auto.Util.Reflection

import public Data.Fin
import public Data.Vect.Dependent

import public Data.SortedMap
import public Data.SortedMap.Dependent
import public Data.SortedSet

import public Language.Reflection.TTImp
import public Language.Reflection.Types

import public Test.DepTyCheck.Gen.Auto.Util.Fin
import public Test.DepTyCheck.Gen.Auto.Util.List
import public Test.DepTyCheck.Gen.Auto.Util.Syntax

%default total

--------------------------------------------
--- Parsing and rebuilding `TTImp` stuff ---
--------------------------------------------

public export
unDPair : TTImp -> (List (Arg False), TTImp)
unDPair (IApp _ (IApp _ (IVar _ `{Builtin.DPair.DPair}) typ) (ILam _ cnt piInfo mbname _ lamTy)) =
    mapFst (MkArg cnt piInfo mbname typ ::) $ unDPair lamTy
unDPair expr = ([], expr)

public export
buildDPair : (rhs : TTImp) -> List (Name, TTImp) -> TTImp
buildDPair = foldr $ \(name, type), res =>
  var `{Builtin.DPair.DPair} .$ type .$ lam (MkArg MW ExplicitArg (Just name) type) res

public export
appFuel : (topmost : Name) -> (fuel : TTImp) -> TTImp
appFuel = app . var

public export
liftList : Foldable f => f TTImp -> TTImp
liftList = foldr (\l, r => `(~(l) :: ~(r))) `([])

--- General purpose instances ---

public export
Eq Namespace where
  MkNS xs == MkNS ys = xs == ys

public export
Eq UserName where
  Basic x    == Basic y    = x == y
  Field x    == Field y    = x == y
  Underscore == Underscore = True
  _ == _ = False

public export
Eq Name where
  UN x   == UN y   = x == y
  MN x n == MN y m = x == y && n == m
  NS s n == NS p m = s == p && n == m
  DN x n == DN y m = x == y && n == m

  Nested x n    ==  Nested y m   = x == y && n == m
  CaseBlock x n == CaseBlock y m = x == y && n == m
  WithBlock x n == WithBlock y m = x == y && n == m

  _ == _ = False

---------------------------------------
--- Working around primitive values ---
---------------------------------------

export
primTypeInfo : String -> TypeInfo
primTypeInfo s = MkTypeInfo (UN $ Basic s) [] []

export
typeInfoOfConstant : Constant -> Maybe TypeInfo
typeInfoOfConstant (I _)       = Nothing
typeInfoOfConstant (BI _)      = Nothing
typeInfoOfConstant (I8 _)      = Nothing
typeInfoOfConstant (I16 _)     = Nothing
typeInfoOfConstant (I32 _)     = Nothing
typeInfoOfConstant (I64 _)     = Nothing
typeInfoOfConstant (B8 _)      = Nothing
typeInfoOfConstant (B16 _)     = Nothing
typeInfoOfConstant (B32 _)     = Nothing
typeInfoOfConstant (B64 _)     = Nothing
typeInfoOfConstant (Str _)     = Nothing
typeInfoOfConstant (Ch _)      = Nothing
typeInfoOfConstant (Db _)      = Nothing
typeInfoOfConstant WorldVal    = Nothing
typeInfoOfConstant IntType     = Just $ primTypeInfo "Int"
typeInfoOfConstant IntegerType = Just $ primTypeInfo "Integer"
typeInfoOfConstant Int8Type    = Just $ primTypeInfo "Int8"
typeInfoOfConstant Int16Type   = Just $ primTypeInfo "Int16"
typeInfoOfConstant Int32Type   = Just $ primTypeInfo "Int32"
typeInfoOfConstant Int64Type   = Just $ primTypeInfo "Int64"
typeInfoOfConstant Bits8Type   = Just $ primTypeInfo "Bits8"
typeInfoOfConstant Bits16Type  = Just $ primTypeInfo "Bits16"
typeInfoOfConstant Bits32Type  = Just $ primTypeInfo "Bits32"
typeInfoOfConstant Bits64Type  = Just $ primTypeInfo "Bits64"
typeInfoOfConstant StringType  = Just $ primTypeInfo "String"
typeInfoOfConstant CharType    = Just $ primTypeInfo "Char"
typeInfoOfConstant DoubleType  = Just $ primTypeInfo "Double"
typeInfoOfConstant WorldType   = Nothing

----------------------------------------------
--- Analyzing dependently typed signatures ---
----------------------------------------------

export
argDeps : (args : List NamedArg) -> Elab $ DVect args.length $ SortedSet . Fin . Fin.finToNat
argDeps args = foldlM (\curr, idx => (curr <+>) <$> tryToDelete idx (index idx curr)) neutral $ allFins' args.length where

  %unbound_implicits off -- this is needed to be able to use `args` (i.e. lowercase) variable in signatures

  filteredArgs : (excluded : SortedSet $ Fin args.length) -> List NamedArg
  filteredArgs excluded = filterI' args $ \idx, _ => not $ contains idx excluded

  partialSig : (retTy : TTImp) -> (excluded : SortedSet $ Fin args.length) -> TTImp
  partialSig retTy = piAll retTy . map {name $= Just} . filteredArgs

  partialApp : (appliee : Name) -> (excluded : SortedSet $ Fin args.length) -> TTImp
  partialApp n = appNames n . map name . filteredArgs

  fullSig : (retTy : TTImp) -> TTImp
  fullSig t = partialSig t empty

  fullApp : (appliee : Name) -> TTImp
  fullApp n = partialApp n empty

  defaultRet : TTImp
  defaultRet = `(Builtin.Unit)

  -- check that *meaning* of types are preversed after excluding some of arguments
  preservationCheckSig : (excluded : SortedSet $ Fin args.length) -> TTImp
  preservationCheckSig excluded =
    pi (MkArg MW ExplicitArg .| Just full .| fullSig defaultRet) $
    pi (MkArg MW ExplicitArg .| Just part .| partialSig defaultRet excluded) $
    fullSig $
    `(Builtin.Equal) .$ fullApp full .$ partialApp part excluded
    where
      full, part : Name
      full = MN "full" 1
      part = MN "part" 1

  tryToDelete : (idx : Fin args.length) -> (idxDeps : SortedSet $ Fin $ finToNat idx) ->
                Elab $ DVect args.length $ SortedSet . Fin . Fin.finToNat

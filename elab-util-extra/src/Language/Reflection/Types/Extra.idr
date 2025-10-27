module Language.Reflection.Types.Extra

import Data.List.Quantifiers
import Language.Reflection.Expr
import Language.Reflection.Logging
import Language.Reflection.Util
import Syntax.IHateParens

%default total

||| Type's constructor
public export
(.Con) : TypeInfo -> Type
(.Con) t = Con t.arty t.args

||| Apply all arguments as specified in AppArgs to TTImp
public export
appArgs : TTImp -> AppArgs a -> TTImp
appArgs t (x :: xs) = appArgs (appArg t x) xs
appArgs t []        = t

||| Apply all arguments as specified in AppArgs to TTImp
public export
appArgs' : TTImp -> AppArgs a -> TTImp
appArgs' t ((AutoApp (Implicit _ _)) :: xs) = appArgs' t xs
appArgs' t (x :: xs) = appArgs (appArg t x) xs
appArgs' t []        = t

||| Convert MissingInfo for compatibility with `cleanupNamedHoles`
public export
cleanupMissing : MissingInfo p -> MissingInfo (Expr.cleanupNamedHoles <$> p)
cleanupMissing Auto = Auto
cleanupMissing Implicit = Implicit
cleanupMissing Deflt = Deflt

||| Run `cleanupNamedHoles` over all `AppArg`'s `TTImp`s
public export
cleanupAppArg : AppArg a -> AppArg (cleanupArg a)
cleanupAppArg (NamedApp n s) = NamedApp n $ cleanupNamedHoles s
cleanupAppArg (AutoApp s) = AutoApp $ cleanupNamedHoles s
cleanupAppArg (Regular s) = Regular $ cleanupNamedHoles s
cleanupAppArg (Missing x) = Missing $ cleanupMissing x

||| Run `cleanupNamedHoles` over all `AppArgs`'s `TTImp`s
public export
cleanupAppArgs : {0 n : Nat} -> {0 a : Vect n Arg} -> AppArgs a -> AppArgs (map Expr.cleanupArg a)
cleanupAppArgs [] = []
cleanupAppArgs (x :: xs) = cleanupAppArg x :: cleanupAppArgs xs

||| Run `cleanupNamedHoled` over all `Con`'s `TTImp`s
public export
cleanupCon : Con a b -> Con a (map Expr.cleanupArg b)
cleanupCon = { args $= map cleanupArg, typeArgs $= cleanupAppArgs }

||| Run `cleanupNamedHoles` over all `TypeInfo`'s `TTImp`s
public export
cleanupTypeInfo : TypeInfo -> TypeInfo
cleanupTypeInfo = {args $= map cleanupArg, cons $= map cleanupCon}

||| Given a type name to which constructor belongs, calculate its signature
public export
conSig : Con _ _ -> Name -> TTImp
conSig con ty = piAll .| appArgs (var ty) con.typeArgs .| toList con.args

||| Given a type name to which constructor belongs, calculate its ITy
public export
conITy : Name -> Con _ ags -> ITy
conITy retTy con = mkTy .| dropNS con.name .| conSig con retTy

||| Generate a declaration from TypeInfo
public export
(.decl) : TypeInfo -> Decl
(.decl) ti =
  iData Public ti.name tySig [] conITys
  where
    tySig = piAll type $ toList ti.args
    conITys = toList $ conITy ti.name <$> ti.cons

||| Generate AppArg for given Arg, substituting names for values if present
public export
(.appArg) : (arg : Arg) -> (0 _ : IsNamedArg arg) => (Name -> TTImp) -> SortedMap Name TTImp -> AppArg arg
(.appArg) (MkArg count piInfo (Just n) type) f argVals = do
  let val = fromMaybe (f n) $ lookup n argVals
  case piInfo of
    ExplicitArg => Regular val
    AutoImplicit => AutoApp val
    _ => NamedApp n val

public export
IsFullyNamedCon : Con _ _ -> Type
IsFullyNamedCon c = All IsNamedArg c.args

public export
isFullyNamedCon : (c : Con _ _) -> Dec $ IsFullyNamedCon c
isFullyNamedCon c = all isNamedArg c.args

public export
record IsFullyNamedType (ti : TypeInfo) where
  constructor ItIsFullyNamed
  argsAreNamed : All IsNamedArg ti.args
  consAreNamed : All IsFullyNamedCon ti.cons

public export
isFullyNamedType : (ti : TypeInfo) -> Dec $ IsFullyNamedType ti
isFullyNamedType ti = do
  let Yes aan = all isNamedArg ti.args
  | No cntr => No (\ifnt => cntr ifnt.argsAreNamed)
  let Yes can = all isFullyNamedCon ti.cons
  | No cntr => No (\ifnt => cntr ifnt.consAreNamed)
  Yes $ ItIsFullyNamed aan can


||| Generate AppArgs for given argument vector, substituting names for values
||| if present
public export
(.appArgs) : (args: Vect _ Arg) -> (0 _ : All IsNamedArg args) => (Name -> TTImp) -> SortedMap Name TTImp -> AppArgs args
(.appArgs) [] f argVals = []
(.appArgs) (x :: xs) @{p :: ps} f argVals = x.appArg f argVals :: xs.appArgs f argVals

namespace TypeInfoInvoke
  ||| Generate type invocation, substituting argument values
  public export
  (.invoke) : (ti: TypeInfo) -> (0 _ : IsFullyNamedType ti) => (Name -> TTImp) -> SortedMap Name TTImp -> TTImp
  (.invoke) t @{pt} f vals = do
    appArgs (var t.name) $ t.args.appArgs @{pt.argsAreNamed} f vals

namespace ConInvoke
  ||| Generate constructor invocation, substituting argument values
  public export
  (.invoke) : (con : Con _ _) -> (0 _ : IsFullyNamedCon con) => (Name -> TTImp) -> SortedMap Name TTImp -> TTImp
  (.invoke) con @{conP} f vals = appArgs (var con.name) $ con.args.appArgs f vals

public export
LogPosition TypeInfo where
  logPosition = show . name

public export
LogPosition (Con aty ags) where
  logPosition = show . dropNS . name

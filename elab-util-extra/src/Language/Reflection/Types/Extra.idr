module Language.Reflection.Types.Extra

import Language.Reflection.Util
import Syntax.IHateParens

||| Type's constructor
public export
(.Con) : TypeInfo -> Type
(.Con) t = Con t.arty t.args

||| Apply all arguments as specified in AppArgs to TTImp
public export
appArgs : TTImp -> AppArgs a -> TTImp
appArgs t (x :: xs) = appArgs (appArg t x) xs
appArgs t []        = t

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
(.appArg) : (arg : Arg) -> (Name -> TTImp) -> SortedMap Name TTImp -> Maybe $ AppArg arg
(.appArg) (MkArg count piInfo (Just n) type) f argVals = do
  let val = fromMaybe (f n) $ lookup n argVals
  Just $ case piInfo of
    ExplicitArg => Regular val
    AutoImplicit => AutoApp val
    _ => NamedApp n val
(.appArg) (MkArg count piInfo Nothing type) f argVals = Nothing

||| Generate AppArgs for given argument vector, substituting names for values
||| if present
public export
(.appArgs) : (args: Vect _ Arg) -> (Name -> TTImp) -> SortedMap Name TTImp -> Maybe $ AppArgs args
(.appArgs) [] f argVals = Just []
(.appArgs) (x :: xs) f argVals = [| x.appArg f argVals :: xs.appArgs f argVals |]

namespace TypeInfoInvoke
  ||| Generate type invocation, substituting argument values
  public export
  (.invoke) : TypeInfo -> (Name -> TTImp) -> SortedMap Name TTImp -> TTImp
  (.invoke) t f vals =
    fromMaybe `(_) $ appArgs (var t.name) <$> t.args.appArgs f vals

namespace ConInvoke
  ||| Generate constructor invocation, substituting argument values
  public export
  (.invoke) : Con _ _ -> (Name -> TTImp) -> SortedMap Name TTImp -> TTImp
  (.invoke) con f vals =
    fromMaybe `(_) $ appArgs (var con.name) <$> con.args.appArgs f vals


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
(.appArg) : (arg : Arg) -> SortedMap Name TTImp -> Maybe $ AppArg arg
(.appArg) (MkArg count piInfo (Just n) type) argVals = do
  let val = fromMaybe (var n) $ lookup n argVals
  Just $ case piInfo of
    ExplicitArg => Regular val
    AutoImplicit => AutoApp val
    _ => NamedApp n val
(.appArg) (MkArg count piInfo Nothing type) argVals = Nothing

||| Generate AppArg for given Arg, substituting names for values if present
||| and binding otherwise
public export
(.appArgBind) : (arg : Arg) -> SortedMap Name TTImp -> Maybe $ AppArg arg
(.appArgBind) (MkArg count piInfo (Just n) type) argVals = do
  let val = fromMaybe (bindVar n) $ lookup n argVals
  Just $ case piInfo of
    ExplicitArg => Regular val
    AutoImplicit => AutoApp val
    _ => NamedApp n val
(.appArgBind) (MkArg count piInfo Nothing type) argVals = Nothing

||| Generate AppArg for given Arg, substituting names for values if present
||| and using hole otherwise
public export
(.appArgHole) : (arg : Arg) -> SortedMap Name TTImp -> Maybe $ AppArg arg
(.appArgHole) (MkArg count piInfo (Just n) type) argVals = do
  let val = fromMaybe (Implicit EmptyFC False) $ lookup n argVals
  Just $ case piInfo of
    ExplicitArg => Regular val
    AutoImplicit => AutoApp val
    _ => NamedApp n val
(.appArgHole) (MkArg count piInfo Nothing type) argVals = Nothing

||| Generate AppArgs for given argument vector, substituting names for values
||| if present
public export
(.appArgs) : (args: Vect _ Arg) -> SortedMap Name TTImp -> Maybe $ AppArgs args
(.appArgs) [] argVals = Just []
(.appArgs) (x :: xs) argVals = [| x.appArg argVals :: xs.appArgs argVals |]

||| Generate AppArgs for given argument vector, substituting names for values
||| if present, and binding otherwise
public export
(.appArgsBind) :
  (args: Vect _ Arg) ->
  SortedMap Name TTImp ->
  Maybe $ AppArgs args
(.appArgsBind) [] argVals = Just []
(.appArgsBind) (x :: xs) argVals =
  [| x.appArgBind argVals :: xs.appArgsBind argVals |]

||| Generate AppArgs for given argument vector, substituting names for values
||| if present, and using hole otherwise
public export
(.appArgsHole) :
  (args: Vect _ Arg) ->
  SortedMap Name TTImp ->
  Maybe $ AppArgs args
(.appArgsHole) [] argVals = Just []
(.appArgsHole) (x :: xs) argVals =
  [| x.appArgHole argVals :: xs.appArgsHole argVals |]

namespace TypeInfoInvoke
  ||| Generate type invocation, substituting argument values
  public export
  (.invoke) : TypeInfo -> SortedMap Name TTImp -> TTImp
  (.invoke) t vals =
    fromMaybe `(_) $ appArgs (var t.name) <$> t.args.appArgs vals

  ||| Generate binding type invocation, substituting argument values
  public export
  (.invokeBind) : TypeInfo -> SortedMap Name TTImp -> TTImp
  (.invokeBind) t vals =
    fromMaybe `(_) $ appArgs (var t.name) <$> t.args.appArgsBind vals

namespace ConInvoke
  ||| Generate constructor invocation, substituting argument values
  public export
  (.invoke) : Con _ _ -> SortedMap Name TTImp -> TTImp
  (.invoke) con vals =
    fromMaybe `(_) $ appArgs (var con.name) <$> con.args.appArgs vals

  ||| Generate binding constructor invocation, substituting argument values
  public export
  (.invokeBind) : Con _ _ -> SortedMap Name TTImp -> TTImp
  (.invokeBind) con vals =
    fromMaybe `(_) $ appArgs (var con.name) <$> con.args.appArgsBind vals

  public export
  (.invokeHole) : Con _ _ -> SortedMap Name TTImp -> TTImp
  (.invokeHole) con vals =
    fromMaybe `(_) $ appArgs (var con.name) <$> con.args.appArgsHole vals


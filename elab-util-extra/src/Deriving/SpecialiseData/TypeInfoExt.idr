module Deriving.SpecialiseData.TypeInfoExt

import Language.Reflection.Compat
import Language.Reflection.Expr

||| Generate an AnyApp for given Arg, with the argument value either
||| retrieved from the map if present or generated with `fallback`
(.appWith) :
  (arg : Arg) ->
  (0 _ : IsNamedArg arg) =>
  (fallback : Name -> TTImp) ->
  (argValues : SortedMap Name TTImp) ->
  AnyApp
(.appWith) arg@(MkArg _ _ (Just n) _) f argVals =
  appArg arg $ fromMaybe (f n) $ lookup n argVals

||| Generate a List AnyApp for given argument List,
||| with arguments retrieved from the map if present or generated with `fallback`
export
(.appsWith) :
  (args: List Arg) ->
  (0 _ : All IsNamedArg args) =>
  (fallback : Name -> TTImp) ->
  (argValues : SortedMap Name TTImp) ->
  List AnyApp
(.appsWith) [] _ _ = []
(.appsWith) (x :: xs) @{_ :: _} f argVals =
  x.appWith f argVals :: xs.appsWith f argVals

namespace TypeInfoInvoke
  ||| Returns a full application of the given type constructor
  ||| with argument values sourced from `argValues`
  ||| or generated with `fallback` if not present
  export
  (.apply) :
    (ti : TypeInfo) ->
    (0 tiN : AllTyArgsNamed ti) =>
    (fallback : Name -> TTImp) ->
    (argValues : SortedMap Name TTImp) ->
    TTImp
  (.apply) t f vals = do
    reAppAny (var t.name) $ t.args.appsWith @{tiN.tyArgsNamed} f vals

namespace ConInvoke
  ||| Returns a full application of the given constructor
  ||| with argument values sourced from `argValues`
  ||| or generated with `fallback` if not present
  export
  (.apply) :
    (con : Con) ->
    (0 _ : ConArgsNamed con) =>
    (fallback : Name -> TTImp) ->
    (argValues : SortedMap Name TTImp) ->
    TTImp
  (.apply) con f vals = reAppAny (var con.name) $ con.args.appsWith f vals @{conArgsNamed}

module Deriving.SpecialiseData.Helpers

import Language.Reflection.Compat
import Language.Reflection.Expr

export
prependS : String -> Name -> Name
prependS s n = UN $ Basic $ s ++ show n

||| Given a sequence of arguments, return list of argument name-BindVar pairs
export
argsToBindMap : Foldable f => f Arg -> List (Name, TTImp)
argsToBindMap = foldMap $ toList . map (\y => (y, bindVar y)) . name

||| Specialistaion-related constructor argument metadata
public export
record ArgMeta where
  constructor MkAMeta
  ||| The argument's type can be substituted by specialised type invocation
  isRecursiveArg : Bool

||| Specialisation-related constructor metadata
public export
record ConMeta where
  constructor MkCMeta
  ||| Metadata for each argument
  argMeta : List ArgMeta
  ||| Replacements to transform original argument's type to specialised type
  mToPRenames : SortedMap Name TTImp
  ||| Replacement to transform specialised type to original argument's type
  pToMRenames : SortedMap Name TTImp

export
hasRecursiveArgs : ConMeta -> Bool
hasRecursiveArgs = any isRecursiveArg . argMeta

export
countRecursiveArgs : ConMeta -> Nat
countRecursiveArgs = count isRecursiveArg  . argMeta

export
recursiveArgNames : Con -> ConMeta -> List Name
recursiveArgNames con meta = do
  let recursiveArgPairs = List.filter (isRecursiveArg . snd) $ zip con.args meta.argMeta
  fromMaybe "" . name . fst <$> recursiveArgPairs

||| Specialisation-related type metadata
public export
record TypeMeta where
  constructor MkTyMeta
  ||| Specialisation-related metadata for each constructor
  conMeta : List ConMeta

||| Generate a constructor binding where only recursive arguments are bound.
||| Said arguments are also aliased via `alias` function.
export
bindConRecArgsAliased : Con -> ConMeta -> (Name -> Name) -> TTImp
bindConRecArgsAliased con meta alias =
  reAppAny (var con.name) $ processArg <$> zip con.args meta.argMeta
  where
  maybeBind : Arg -> ArgMeta -> TTImp
  maybeBind a am = if isRecursiveArg am then bindVar $ alias $ fromMaybe "" a.name else `(_)

  processArg : (Arg, ArgMeta) -> AnyApp
  processArg (a@(MkArg _ ExplicitArg _ _), am) = PosApp $ maybeBind a am
  processArg (a, am) = NamedApp (fromMaybe "" a.name) $ maybeBind a am

||| Make an argument omega implicit if it is explicit
export
hideExplicitArg : Arg -> Arg
hideExplicitArg a = { piInfo := if a.piInfo == ExplicitArg then ImplicitArg else a.piInfo } a

||| Make a type argument zero-count
export
makeTypeArgM0 : Arg -> Arg
makeTypeArgM0 a = { count := if a.type == `(Type) then M0 else a.count } a

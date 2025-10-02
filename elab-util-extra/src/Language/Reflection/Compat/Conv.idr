module Language.Reflection.Compat.Conv

import public Data.DPair
import Data.Vect.Quantifiers

import public Language.Reflection.Compat as Old
import public Language.Reflection.Types as New

import public Syntax.IHateParens.Function
import public Syntax.IHateParens.List
import public Syntax.IHateParens.Vect

%default total

pushIn' : (0 xs : Vect n a) -> All p xs -> Vect n $ Exists p
pushIn' []      []      = []
pushIn' (x::xs) (p::ps) = Evidence x p :: pushIn' xs ps

appArgs : TTImp -> AppArgs ars -> TTImp
appArgs to aars = foldl (\acc, aar => appArg acc aar.snd) to $ pushIn' ars aars

namespace TypeInfo

  public export %inline
  0 OldTypeInfoWithNames : Type
  OldTypeInfoWithNames = Subset Old.TypeInfo $ All IsNamedArg . TypeInfo.args

  oldToNewCon : Old.Con -> Maybe $ New.Con tyArity tyArs
  oldToNewCon $ MkCon nm ars ty = do
    Just $ MkCon nm ? ?newArs ?tyAars

  export
  oldToNew : OldTypeInfoWithNames -> New.TypeInfo
  oldToNew $ MkTypeInfo nm ars cns `Element` nars = do
    let ars = pushIn ars nars <&> \(Element ar@(MkArg {name=Just n, _}) _) => (ar, n)
    let (ars', arNames') = unzip $ fromList ars
    MkTypeInfo nm ? ars' arNames' $ mapMaybe oldToNewCon cns

  -- We need to take the type name because the new constructors representation does not have it
  newToOldCon : (tyName : Name) -> New.Con arity ars -> Old.Con
  newToOldCon tyName $ MkCon nm _ ars tyArgs = do
    MkCon nm ars.asList (appArgs (var nm) tyArgs)

  export
  newToOld : New.TypeInfo -> OldTypeInfoWithNames
  newToOld $ MkTypeInfo nm arty ars arNames cns = do
    let Element ars' nars' = pullOut $ toList $ zip ars arNames <&> \(MkArg c p _ t, n) => MkArg c p (Just n) t `Element` ItIsNamed
    MkTypeInfo nm ars' (newToOldCon nm <$> cns) `Element` nars'

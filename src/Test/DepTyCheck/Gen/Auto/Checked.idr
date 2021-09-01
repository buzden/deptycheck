module Test.DepTyCheck.Gen.Auto.Checked

import public Control.Monad.Reader
import public Control.Monad.Trans
import public Control.Monad.Writer

import public Data.Vect.Extra
import public Data.SortedMap
import public Data.SortedSet

import public Language.Reflection.Types

import public Syntax.WithProof

import public Test.DepTyCheck.Gen.Auto.Util

%default total

-----------------------------------------------------
--- Data types for the safe signature formulation ---
-----------------------------------------------------

public export
data ArgExplicitness = ExplicitArg | ImplicitArg

public export
Eq ArgExplicitness where
  ExplicitArg == ExplicitArg = True
  ImplicitArg == ImplicitArg = True
  _ == _ = False

namespace ArgExplicitness

  public export
  (.toTT) : ArgExplicitness -> PiInfo a
  (.toTT) ExplicitArg = ExplicitArg
  (.toTT) ImplicitArg = ImplicitArg

------------------------------------------------------------------
--- Datatypes to describe signatures after checking user input ---
------------------------------------------------------------------

public export
data NamesOrigin = CustomNames | FromDataDef

public export
record GenSignature (nso : NamesOrigin) where
  constructor MkGenSignature
  targetType : TypeInfo
  givenParams : SortedMap (Fin targetType.args.length) $ case nso of
                                                           CustomNames => (ArgExplicitness, Name)
                                                           FromDataDef => ArgExplicitness

namespace GenSignature

  characteristics : GenSignature cn -> (String, List Nat)
  characteristics (MkGenSignature ty giv) = (show ty.name, toNatList $ keys giv)

public export
Eq (GenSignature cn) where
  (==) = (==) `on` characteristics

public export
Ord (GenSignature cn) where
  compare = comparing characteristics

public export
record GenExternals where
  constructor MkGenExternals
  externals : SortedSet $ GenSignature CustomNames

-----------------------------------
--- "Canonical" functions stuff ---
-----------------------------------

--- Main interfaces ---

public export
interface Monad m => CanonicGen m where
  callGen : {nso : _} -> (sig : GenSignature nso) -> Vect sig.givenParams.asList.length TTImp -> m TTImp

--- Canonic signature functions --

-- Must respect names from the `givenParams` field, at least for implicit parameters
export
canonicSig : GenSignature FromDataDef -> TTImp
canonicSig sig = piAll returnTy $ arg <$> toList sig.givenParams where
  -- TODO Check that the resulting `TTImp` reifies to a `Type`? During this check, however, all types must be present in the caller's context.

  arg : (Fin sig.targetType.args.length, ArgExplicitness) -> Arg False
  arg (idx, expl) = let MkArg {name, type, _} = index' sig.targetType.args idx in MkArg MW expl.toTT (Just name) type

  returnTy : TTImp
  returnTy = var `{Test.DepTyCheck.Gen.Gen} .$ buildDPair targetTypeApplied generatedArgs where

    targetTypeApplied : TTImp
    targetTypeApplied = foldr apply (var sig.targetType.name) $ reverse $ sig.targetType.args <&> \(MkArg {name, piInfo, _}) =>
                          case piInfo of
                            ExplicitArg   => (.$ var name)
                            ImplicitArg   => \f => namedApp f name $ var name
                            DefImplicit _ => \f => namedApp f name $ var name
                            AutoImplicit  => (`autoApp` var name)

    generatedArgs : List (Name, TTImp)
    generatedArgs = mapMaybeI' sig.targetType.args $ \idx, (MkArg _ _ name type) =>
                      case lookup idx sig.givenParams of
                        Nothing => Just (name, type)
                        Just _  => Nothing

callCanonicGen : {nso : _} -> (sig : GenSignature nso) -> (topmost : TTImp) -> Vect sig.givenParams.asList.length TTImp -> TTImp
callCanonicGen sig topmost values =
  let (givenParams ** prfAsSig) = @@ sig.givenParams.asList in
  foldl (flip apply) topmost $ flip mapWithPos values $ \valueIdx, value =>
    let (paramIdx, info) = index' givenParams $ rewrite sym prfAsSig in valueIdx in
    let (expl, name) : (ArgExplicitness, Name) = case nso of
                                                   CustomNames => info
                                                   FromDataDef => (info, nm $ index' sig.targetType.args paramIdx)
    in case expl of
      ExplicitArg => (.$ value)
      ImplicitArg => \f => namedApp f name value

  where
    nm : Arg True -> Name -- workaround of some type inference bug
    nm = name

--- The main meat for derivation ---

export
deriveCanonical : CanonicGen m => GenSignature nso -> m Decl
deriveCanonical sig = do
  ?deriveCanonical_rhs

--- Particular implementations producing the-meat-derivation-function clojure ---

namespace ClojuringCanonicImpl

  ClojuringContext : (Type -> Type) -> Type
  ClojuringContext m =
    ( MonadReader (SortedMap (GenSignature CustomNames) Name) m
    , MonadWriter (SortedMap (GenSignature CustomNames) $ Lazy Decl) m
    )

  canonicGenExpr : ClojuringContext m => {nso : _} -> GenSignature nso -> m TTImp
  canonicGenExpr sig = ?canonicGenExpr_rhs

  export
  ClojuringContext m => CanonicGen m where
    callGen sig values = pure $ callCanonicGen sig !(canonicGenExpr sig) values

--- Canonic-dischagring function ---

export
runCanonic : GenExternals -> (forall m. CanonicGen m => m a) -> Elab (a, List Decl)
runCanonic exts calc = ?runCanonic_rhs

module Test.DepTyCheck.Gen.Auto.Checked

import public Control.Monad.Reader
import public Control.Monad.Trans
import public Control.Monad.Writer

import public Data.DPair

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

--- Simplest `Gen` signature, user for requests ---

public export
record GenSignature where
  constructor MkGenSignature
  targetType : TypeInfo
  givenParams : SortedSet $ Fin targetType.args.length

--- `Gen` signature containing info about params explicitness and their names ---

public export
record ExternalGenSignature where
  constructor MkExternalGenSignature
  targetType : TypeInfo
  givenParams : SortedMap (Fin targetType.args.length) (ArgExplicitness, Name)

namespace ExternalGenSignature

  characteristics : ExternalGenSignature -> (String, List Nat)
  characteristics $ MkExternalGenSignature ty giv = (show ty.name, toNatList $ keys giv)

public export
Eq ExternalGenSignature where
  (==) = (==) `on` characteristics

public export
Ord ExternalGenSignature where
  compare = comparing characteristics

internalise : (extSig : ExternalGenSignature) -> Subset GenSignature $ \sig => sig.givenParams.asList.length = extSig.givenParams.asList.length
internalise $ MkExternalGenSignature ty giv = Element (MkGenSignature ty $ keySet giv) $ believe_me $ the (0 = 0) Refl
            -- Dirty-dirty `believe_me` hack! It's true but hard to prove with the current implementation

externalise : GenSignature -> ExternalGenSignature
externalise $ MkGenSignature ty giv = MkExternalGenSignature ty $ fromList $ (\idx => (idx, ExplicitArg, argName $ index' ty.args idx)) <$> giv.asList

-----------------------------------
--- "Canonical" functions stuff ---
-----------------------------------

--- Canonic signature functions --

-- Must respect names from the `givenParams` field, at least for implicit parameters
export
canonicSig : GenSignature -> TTImp
canonicSig sig = piAll returnTy $ arg <$> SortedSet.toList sig.givenParams where
  -- TODO Check that the resulting `TTImp` reifies to a `Type`? During this check, however, all types must be present in the caller's context.

  arg : Fin sig.targetType.args.length -> Arg False
  arg idx = let MkArg {name, type, _} = index' sig.targetType.args idx in MkArg MW ExplicitArg (Just name) type

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
    generatedArgs = mapMaybeI' sig.targetType.args $ \idx, (MkArg _ _ name type) => ifThenElse (contains idx sig.givenParams) Nothing $ Just (name, type)

callExternalGen : (sig : ExternalGenSignature) -> (topmost : TTImp) -> Vect sig.givenParams.asList.length TTImp -> TTImp
callExternalGen sig topmost values =
  let (givenParams ** prfAsSig) = @@ sig.givenParams.asList in
  foldl (flip apply) topmost $ flip mapWithPos values $ \valueIdx, value =>
    let (_, expl, name) = index' givenParams $ rewrite sym prfAsSig in valueIdx
    in case expl of
      ExplicitArg => (.$ value)
      ImplicitArg => \f => namedApp f name value

--- Main interfaces ---

public export
interface Monad m => CanonicGen m where
  callGen : (sig : GenSignature) -> Vect sig.givenParams.asList.length TTImp -> m TTImp

export
internalGenCallingLambda : CanonicGen m => ExternalGenSignature -> m TTImp
internalGenCallingLambda sig = foldr (map . mkLam) call sig.givenParams.asList where

  mkLam : (Fin sig.targetType.args.length, ArgExplicitness, Name) -> TTImp -> TTImp
  mkLam (idx, expl, name) = lam $ MkArg MW expl.toTT (Just name) (index' sig.targetType.args idx).type

  call : m TTImp
  call = let Element intSig prf = internalise sig in
         callGen intSig $ rewrite prf in fromList sig.givenParams.asList <&> \(_, _, name) => var name

--- The main meat for derivation ---

export
deriveCanonical : CanonicGen m => GenSignature -> m Decl
deriveCanonical sig = do
  ?deriveCanonical_rhs

--- Particular implementations producing the-meat-derivation-function clojure ---

namespace ClojuringCanonicImpl

  ClojuringContext : (Type -> Type) -> Type
  ClojuringContext m =
    ( MonadReader (SortedMap ExternalGenSignature Name) m
    , MonadWriter (SortedMap ExternalGenSignature $ Lazy Decl) m
    )

  canonicGenExpr : ClojuringContext m => GenSignature -> m TTImp
  canonicGenExpr sig = ?canonicGenExpr_rhs

  export
  ClojuringContext m => CanonicGen m where
    callGen sig values = ?callGen_impl
                         -- First, need to known whether do we have an external generator for the given signature.
                         -- If yes, just use `callExternalGen` for it.
                         -- If not, either use `callExternalGen` for an externalised version,
                         --   or have a separate function equivalent to `callExternalGen` applied to an externalised signature.
                         -- originally was `pure $ callExternalGen sig !(canonicGenExpr sig) values`

--- Canonic-dischagring function ---

export
runCanonic : SortedMap ExternalGenSignature Name -> (forall m. CanonicGen m => m a) -> Elab (a, List Decl)
runCanonic exts calc = ?runCanonic_rhs

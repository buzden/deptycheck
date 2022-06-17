||| Interfaces for using a derivator
module Test.DepTyCheck.Gen.Auto.Derive

import public Control.Monad.Error.Interface

import public Data.SortedMap
import public Data.SortedMap.Dependent
import public Data.SortedSet

import public Test.DepTyCheck.Gen.Auto.Util

%default total

---------------------------------------------------
--- Simplest `Gen` signature, user for requests ---
---------------------------------------------------

public export
record GenSignature where
  constructor MkGenSignature
  targetType : TypeInfo
  givenParams : SortedSet $ Fin targetType.args.length

namespace GenSignature

  export
  characteristics : GenSignature -> (String, List Nat)
  characteristics $ MkGenSignature ty giv = (show ty.name, toNatList giv)

  -- A signature with no params; actually, a hack, in particular, for additional gens context.
  export
  dummySig : GenSignature
  dummySig = MkGenSignature (typeInfoForPrimType WorldType) empty

public export
Eq GenSignature where
  (==) = (==) `on` characteristics

public export
Ord GenSignature where
  compare = comparing characteristics

nameForGen' : GenSignature -> String
nameForGen' sig = let (ty, givs) = characteristics sig in "<\{ty}>\{show givs}"
-- I'm using `UN` but containing chars that cannot be present in the code parsed from the Idris frontend.

export
nameForGen : GenSignature -> Name
nameForGen = UN . Basic . nameForGen'

--------------------------------------------
--- Additional generators representation ---
--------------------------------------------

public export
record AdditionalGensFor (0 sig : GenSignature) where
  constructor MkAdditionalGens
  additionalGens : SortedSet (Fin sig.targetType.args.length, GenSignature)
  universalGen : Bool

namespace TransportAdditionalGens

  -- This type should consider all non-trivial usages of `sig` parameter inside the `AdditionalGensFor sig` record.
  -- In a tight case is can be, say, `So (sig == sig')`, but this may lead to a lot of useless runtime checks during `tryTranspCompatSig`.
  export
  CompatSigs : (sig, sig' : GenSignature) -> Type
  CompatSigs sig sig' = So (sig.targetType.name == sig'.targetType.name && sig.targetType.args.length == sig'.targetType.args.length)

  export
  decCompatSigs : (sig, sig' : GenSignature) -> Dec $ CompatSigs sig sig'
  decCompatSigs _ _ = decSo _

  export
  transpCompatSig : CompatSigs sig sig' -> AdditionalGensFor sig -> AdditionalGensFor sig'
  transpCompatSig _ sig = believe_me sig

  export
  tryTranspCompatSig : Elaboration m => {sig, sig' : _} -> AdditionalGensFor sig -> m $ AdditionalGensFor sig'
  tryTranspCompatSig adds with (decCompatSigs sig sig')
    _ | Yes p = pure $ transpCompatSig p adds
    _ | No _  = fail "Unable to change signatire for additional gens: incompatible signatures"

public export
Semigroup (AdditionalGensFor sig) where
  l <+> r = MkAdditionalGens
            { additionalGens = ((<+>) `on` additionalGens) l r
            , universalGen = l.universalGen || r.universalGen
            }

public export
Monoid (AdditionalGensFor sig) where
  neutral = MkAdditionalGens empty False

export
Eq (AdditionalGensFor sig) where
  al == ar = al.additionalGens == ar.additionalGens && al.universalGen == ar.universalGen

public export
justUniversalGen : AdditionalGensFor sig
justUniversalGen = MkAdditionalGens empty True

----------------------
--- Main interface ---
----------------------

public export
interface Elaboration m => CanonicGen m where
  callGen : {outerSig : GenSignature} ->
            (sig : GenSignature) ->
            (fuel : TTImp) ->
            Vect sig.givenParams.size TTImp -> m (TTImp, AdditionalGensFor outerSig)

export
CanonicGen m => MonadTrans t => Monad (t m) => CanonicGen (t m) where
  callGen sig fuel params = lift $ callGen sig fuel params

--- Low-level derivation interface ---

export
canonicSig : (sig : GenSignature) -> AdditionalGensFor sig -> TTImp
canonicSig sig addition = piAll returnTy $
  MkArg MW ExplicitArg Nothing `(Data.Fuel.Fuel) :: (arg <$> SortedSet.toList sig.givenParams) ++ map extGenArg (universal ++ additional) where
  -- TODO Check that the resulting `TTImp` reifies to a `Type`? During this check, however, all types must be present in the caller's context.

  arg : Fin sig.targetType.args.length -> Arg False
  arg idx = let MkArg {name, type, _} = index' sig.targetType.args idx in MkArg MW ExplicitArg (Just name) type

  returnTy : TTImp
  returnTy = var `{Test.DepTyCheck.Gen.Gen} .$ buildDPair targetTypeApplied generatedArgs where

    targetTypeApplied : TTImp
    targetTypeApplied = foldr apply (var sig.targetType.unpolyName) $ reverse $ sig.targetType.args <&> \(MkArg {name, piInfo, _}) => case piInfo of
                          ExplicitArg   => (.$ var name)
                          ImplicitArg   => \f => namedApp f name $ var name
                          DefImplicit _ => \f => namedApp f name $ var name
                          AutoImplicit  => (`autoApp` var name)

    generatedArgs : List (Name, TTImp)
    generatedArgs = mapMaybeI' sig.targetType.args $ \idx, (MkArg {name, type, _}) =>
                      ifThenElse .| contains idx sig.givenParams .| Nothing .| Just (name, type)

  extGenArg : TTImp -> Arg False
  extGenArg = MkArg MW AutoImplicit Nothing

  universal : List TTImp
  universal = whenT addition.universalGen $
                `(Data.Fuel.Fuel -> Test.DepTyCheck.Gen.Gen (ty : Type ** Data.Fuel.Fuel -> Test.DepTyCheck.Gen.Gen ty))

  additional : List TTImp
  additional = SortedSet.toList addition.additionalGens <&> \(_, subsig) => assert_total $ canonicSig subsig neutral
               -- above totality assertion is valid at least because if addition is `neutral`, no recursive call is done inside

-- Complementary to `canonicSig`
-- TODO to take additional gens into account
export
callCanonic : (0 sig : GenSignature) -> (topmost : Name) -> (fuel : TTImp) -> Vect sig.givenParams.size TTImp -> TTImp
callCanonic _ = foldl app .: appFuel

public export
interface DerivatorCore where
  canonicBody : CanonicGen m => (sig : GenSignature) -> Name -> m (List Clause, AdditionalGensFor sig)

-- NOTE: Implementation of `internalGenBody` cannot know the `Name` of the called gen, thus it cannot use `callInternalGen` function directly.
--       It have to use `callGen` function from `CanonicGen` interface instead.
--       But `callInternalGen` function is still present here because, in some sense, it is a complementary to `internalGenSig`.
--       Internals and changes in the implementation of `internalGenSig` influence on the implementation of `callInternalGen`.

--- Expressions generation utils ---

defArgNames : {sig : GenSignature} -> Vect sig.givenParams.size String
defArgNames = sig.givenParams.asVect <&> show . name . index' sig.targetType.args

export %inline
canonicDefaultLHS : GenSignature -> Name -> (fuel : String) -> TTImp
canonicDefaultLHS sig n fuel = callCanonic sig n .| bindVar fuel .| bindVar <$> defArgNames

export %inline
canonicDefaultRHS : GenSignature -> Name -> (fuel : TTImp) -> TTImp
canonicDefaultRHS sig n fuel = callCanonic sig n fuel .| varStr <$> defArgNames

wrapAdditionalGens : (varUse : String -> TTImp) -> AdditionalGensFor sig -> TTImp -> TTImp
wrapAdditionalGens varUse ags expr = foldl addGen (wrapUni expr) $ SortedSet.toList ags.additionalGens where

  addGen : TTImp -> (a, GenSignature) -> TTImp
  addGen r = autoApp r . varUse . nameForGen' . snd

  wrapUni : TTImp -> TTImp
  wrapUni = if ags.universalGen
              then flip autoApp $ varUse "universal^gen"
              else id

export
wrapAdditionalGensLHS : AdditionalGensFor sig -> TTImp -> TTImp
wrapAdditionalGensLHS = wrapAdditionalGens bindVar

export
wrapAdditionalGensRHS : AdditionalGensFor sig -> TTImp -> TTImp
wrapAdditionalGensRHS = wrapAdditionalGens $ var . UN . Basic -- can't use `varStr` because I expect strings to contain dots

---------------------------------
--- External-facing functions ---
---------------------------------

export
deriveCanonical : DerivatorCore => CanonicGen m => (sig : GenSignature) -> Name -> m (Decl, Decl, AdditionalGensFor sig)
deriveCanonical sig name = do
  when (isPolyType sig.targetType) $
    fail "INTERNAL ERROR: attempt to derive generator for polymorphic type `\{show $ sig.targetType.name}`"
  (bodyClauses, additionalGens) <- canonicBody sig name
  pure (export' name (canonicSig sig additionalGens), def name bodyClauses, additionalGens)

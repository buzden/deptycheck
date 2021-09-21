||| A bridge between a single act of derivation and a user derivation task
module Test.DepTyCheck.Gen.Auto.Checked

import public Control.Monad.Either
import public Control.Monad.Reader
import public Control.Monad.State
import public Control.Monad.Writer
import public Control.Monad.RWS

import public Decidable.Equality

import public Data.DPair

import public Data.Vect.Extra
import public Data.SortedMap
import public Data.SortedSet

import public Language.Reflection.Types

import public Syntax.WithProof

import public Test.DepTyCheck.Gen.Auto.Derive
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

export
internalise : (extSig : ExternalGenSignature) -> Subset GenSignature $ \sig => sig.givenParams.asList.length = extSig.givenParams.asList.length
internalise $ MkExternalGenSignature ty giv = Element (MkGenSignature ty $ keySet giv) $ believe_me $ the (0 = 0) Refl
            -- Dirty-dirty `believe_me` hack! It's true but hard to prove with the current implementation

---------------------------------
--- Infrastructural functions ---
---------------------------------

callExternalGen : (sig : ExternalGenSignature) -> (topmost : Name) -> (fuel : TTImp) -> Vect sig.givenParams.asList.length TTImp -> TTImp
callExternalGen sig topmost fuel values = foldl (flip apply) (appFuel topmost fuel) $ fromList sig.givenParams.asList `zip` values <&> \case
  ((_, ExplicitArg, _   ), value) => (.$ value)
  ((_, ImplicitArg, name), value) => \f => namedApp f name value

callInternalGen : (0 sig : GenSignature) -> (topmost : Name) -> (fuel : TTImp) -> Vect sig.givenParams.asList.length TTImp -> TTImp
callInternalGen _ = foldl app .: appFuel

--- Particular implementations producing the-meat-derivation-function clojure ---

namespace ClojuringCanonicImpl

  ClojuringContext : (Type -> Type) -> Type
  ClojuringContext m =
    ( MonadReader (SortedMap GenSignature (ExternalGenSignature, Name)) m -- external gens
    , MonadState  (SortedMap GenSignature Name) m -- gens already asked to be derived
    , MonadWriter (List Decl, List Decl) m -- function declarations and bodies
    )

  nameForGen : GenSignature -> Name
  nameForGen = (`MN` 0) . show . characteristics

  -- Instead of staticly ensuring that map holds only correct values, we check dynamically, because it's hard to go through `==`-based lookup of maps.
  lookupLengthChecked : (intSig : GenSignature) -> SortedMap GenSignature (ExternalGenSignature, Name) ->
                        Maybe (Name, Subset ExternalGenSignature $ \extSig => extSig.givenParams.asList.length = intSig.givenParams.asList.length)
  lookupLengthChecked intSig m = lookup intSig m >>= \(extSig, name) => (name,) <$>
                                   case decEq extSig.givenParams.asList.length intSig.givenParams.asList.length of
                                      Yes prf => Just $ Element extSig prf
                                      No _    => Nothing

  DerivatorCore => ClojuringContext m => CanFailAtFC m => CanonicGen m where
    callGen sig fuel values = do

      -- look for external gens, and call it if exists
      let Nothing = lookupLengthChecked sig !ask
        | Just (name, Element extSig lenEq) => pure $ callExternalGen extSig name fuel $ rewrite lenEq in values

      -- get the name of internal gen, derive if necessary
      internalGenName <- do

        -- look for existing (already derived) internals, use it if exists
        let Nothing = lookup sig !get
          | Just name => pure name

        -- nothing found, then derive! acquire the name
        let name = nameForGen sig

        do -- actually derive the stuff!

          -- remember that we're responsible for this signature derivation
          modify $ insert sig name

          -- derive declaration and body for the asked signature. It's important to call it AFTER update of the map in the state to not to cycle
          (genFunClaim, genFunBody) <- assert_total $ deriveCanonical sig name

          -- remember the derived stuff
          tell ([genFunClaim], [genFunBody])

        pure name

      -- call the internal gen
      pure $ callInternalGen sig internalGenName fuel values

  --- Canonic-dischagring function ---

  export
  runCanonic : DerivatorCore => SortedMap ExternalGenSignature Name -> (forall m. CanonicGen m => m a) -> Elab (a, List Decl)
  runCanonic exts calc = do
    let exts = SortedMap.fromList $ exts.asList <&> \namedSig => (fst $ internalise $ fst namedSig, namedSig)
    let Right (x, defs, bodies) = runIdentity $ runEitherT $ evalRWST calc exts empty {s=SortedMap GenSignature Name} {w=(_, _)} {m=EitherT (_, _) Identity}
      | Left (fc, msg) => failAt fc msg
    pure (x, defs ++ bodies)

||| A bridge between a single act of derivation and a user derivation task
module Deriving.DepTyCheck.Gen.Checked

import public Control.Monad.Either
import public Control.Monad.Reader
import public Control.Monad.State
import public Control.Monad.State.Tuple
import public Control.Monad.Writer
import public Control.Monad.RWS

import public Data.DPair
import public Data.SortedMap
import public Data.SortedMap.Extra
import public Data.SortedSet

import public Decidable.Equality

import public Deriving.DepTyCheck.Gen.Derive
import public Deriving.DepTyCheck.Util.Reflection

%default total

%ambiguity_depth 4

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
  {auto 0 targetTypeCorrect : AllTyArgsNamed targetType}
  givenParams : SortedMap (Fin targetType.args.length) (ArgExplicitness, Name)

namespace ExternalGenSignature

  export
  characteristics : ExternalGenSignature -> (String, List Nat)
  characteristics $ MkExternalGenSignature ty giv = (show ty.name, toNatList $ keys giv)

public export
Eq ExternalGenSignature where
  (==) = (==) `on` characteristics

public export
Ord ExternalGenSignature where
  compare = comparing characteristics

export
internalise : (extSig : ExternalGenSignature) -> Subset GenSignature $ \sig => sig.givenParams.size = extSig.givenParams.size
internalise $ MkExternalGenSignature ty giv = Element (MkGenSignature ty $ keySet giv) $ keySetSize giv

---------------------------------
--- Infrastructural functions ---
---------------------------------

callExternalGen : (sig : ExternalGenSignature) -> (topmost : Name) -> (fuel : TTImp) -> Vect sig.givenParams.size TTImp -> TTImp
callExternalGen sig topmost fuel values = foldl (flip apply) (appFuel topmost fuel) $ sig.givenParams.asVect `zip` values <&> \case
  ((_, ExplicitArg, _   ), value) => (.$ value)
  ((_, ImplicitArg, name), value) => \f => namedApp f name value

--- Particular implementations producing the-core-derivation-function clojure ---

namespace ClojuringCanonicImpl

  ClojuringContext : (Type -> Type) -> Type
  ClojuringContext m =
    ( MonadReader (SortedMap GenSignature (ExternalGenSignature, Name)) m -- external gens
    , MonadState  (SortedMap GenSignature Name) m                         -- gens already asked to be derived
    , MonadState  (List (GenSignature, Name)) m                           -- queue of gens to be derived
    , MonadState  Bool m                                                  -- flat that there is a need to start derivation loop
    , MonadWriter (List Decl, List Decl) m                                -- function declarations and bodies
    )

  nameForGen : GenSignature -> Name
  nameForGen sig = let (ty, givs) = characteristics sig in UN $ Basic $ "<\{ty}>\{show givs}"
  -- I'm using `UN` but containing chars that cannot be present in the code parsed from the Idris frontend.

  -- Instead of staticly ensuring that map holds only correct values, we check dynamically, because it's hard to go through `==`-based lookup of maps.
  lookupLengthChecked : (intSig : GenSignature) -> SortedMap GenSignature (ExternalGenSignature, Name) ->
                        Maybe (Name, Subset ExternalGenSignature $ \extSig => extSig.givenParams.size = intSig.givenParams.size)
  lookupLengthChecked intSig m = lookup intSig m >>= \(extSig, name) => (name,) <$>
                                   case decEq extSig.givenParams.size intSig.givenParams.size of
                                      Yes prf => Just $ Element extSig prf
                                      No _    => Nothing

  DerivatorCore => ClojuringContext m => Elaboration m => NamesInfoInTypes => CanonicGen m where
    callGen sig fuel values = do

      -- check if we are the first, then we need to start the loop
      startLoop <- get {stateType=Bool}
      -- say that no one needs any more startups, we are in charge
      put False

      -- look for external gens, and call it if exists
      let Nothing = lookupLengthChecked sig !ask
        | Just (name, Element extSig lenEq) => pure $ callExternalGen extSig name (var outmostFuelArg) $ rewrite lenEq in values

      -- get the name of internal gen, derive if necessary
      internalGenName <- do

        -- look for existing (already derived) internals, use it if exists
        let Nothing = SortedMap.lookup sig !get
          | Just name => pure name

        -- nothing found, then derive! acquire the name
        let name = nameForGen sig

        -- remember that we're responsible for this signature derivation
        modify $ insert sig name

        -- remember the task to derive
        modify {stateType=List _} $ (::) (sig, name)

        -- return the name of the newly derived generator
        pure name

      -- if we were first to start the derivation loop, then...
      when startLoop $ do
        -- start the derivation loop itself
        deriveAll
        -- we now are not in charge of the derivation loop, so reset the flag
        put True

      -- call the internal gen
      pure $ callCanonic sig internalGenName fuel values

      where

        deriveOne : (GenSignature, Name) -> m ()
        deriveOne (sig, name) = do

          -- derive declaration and body for the asked signature. It's important to call it AFTER update of the map in the state to not to cycle
          (genFunClaim, genFunBody) <- logBounds "type" [sig] $ assert_total $ deriveCanonical sig name

          -- remember the derived stuff
          tell ([genFunClaim], [genFunBody])

        deriveAll : m ()
        deriveAll = do
          toDerive <- get {stateType=List _}
          put {stateType=List _} []
          for_ toDerive deriveOne
          when (not $ null toDerive) $ assert_total $ deriveAll

  --- Canonic-dischagring function ---

  export
  runCanonic : DerivatorCore => NamesInfoInTypes => SortedMap ExternalGenSignature Name -> (forall m. CanonicGen m => m a) -> Elab (a, List Decl)
  runCanonic exts calc = do
    let exts = SortedMap.fromList $ exts.asList <&> \namedSig => (fst $ internalise $ fst namedSig, namedSig)
    (x, defs, bodies) <- evalRWST exts (empty, empty, True) calc {s=(SortedMap GenSignature Name, List (GenSignature, Name), _)} {w=(_, _)}
    pure (x, defs ++ bodies)

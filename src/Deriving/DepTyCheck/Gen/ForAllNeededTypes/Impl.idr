||| A bridge between a single act of derivation (for a single type) and a user derivation task
module Deriving.DepTyCheck.Gen.ForAllNeededTypes.Impl

import public Control.Monad.Either
import public Control.Monad.Reader
import public Control.Monad.State
import public Control.Monad.State.Tuple
import public Control.Monad.Writer
import public Control.Monad.RWS

import public Data.DPair
import public Data.List.Map
import public Data.SortedMap
import public Data.SortedMap.Extra
import public Data.SortedSet

import public Decidable.Equality

import public Deriving.DepTyCheck.Gen.ForOneType.Interface

%default total

--- Particular implementations producing the-core-derivation-function closure ---

ClosuringContext : (Type -> Type) -> Type
ClosuringContext m =
  ( MonadReader (SortedMap GenSignature (ExternalGenSignature, Name)) m -- external gens
  , MonadState  (ListMap GenSignature Name) m                           -- gens already asked to be derived
  , MonadState  (List (GenSignature, Name)) m                           -- queue of gens to be derived
  , MonadState  NamesInfoInTypes m                                      -- current known types
  , MonadState  ConsRecs m                                              -- recursiveness and consturctor weights for current known types
  , MonadState  Bool m                                                  -- flag that there is a need to start derivation loop
  , MonadState  (SortedSet Name) m                                      -- type names that were asked for deriving their weighting function
  , MonadWriter (List Decl, List Decl) m                                -- function declarations and bodies
  )

nameForGen : GenSignature -> Name
nameForGen sig = let (ty, givs) = characteristics sig in UN $ Basic $ "<\{ty}>\{show givs}"
-- I'm using `UN` but containing chars that cannot be present in the code parsed from the Idris frontend.

-- Instead of staticaly ensuring that map holds only correct values, we check dynamically, because it's hard to go through `==`-based lookup of maps.
lookupLengthChecked : (intSig : GenSignature) -> SortedMap GenSignature (ExternalGenSignature, Name) ->
                      Maybe (Name, Subset ExternalGenSignature $ \extSig => extSig.givenParams.size = intSig.givenParams.size)
lookupLengthChecked intSig m = lookup intSig m >>= \(extSig, name) => (name,) <$>
                                 case decEq extSig.givenParams.size intSig.givenParams.size of
                                    Yes prf => Just $ Element extSig prf
                                    No _    => Nothing

DeriveBodyForType => ClosuringContext m => Elaboration m => DerivationClosure m where

  needWeightFun ty = when (not !(gets $ contains ty.name)) $ do
    modify $ insert ty.name
    _ : ConsRecs <- get
    whenJust (deriveWeightingFun ty) $ tell . mapHom singleton

  callGen sig fuel values = do

    -- check if we are the first, then we need to start the loop
    startLoop <- get {stateType=Bool}
    -- say that no one needs any more startups, we are in charge
    put False

    -- look for external gens, and call it if exists
    let Nothing = lookupLengthChecked sig !ask
      | Just (name, Element extSig lenEq) => do
          logPoint Details "deptycheck.derive.closuring.external" [sig] "is used as an external generator"
          pure (callExternalGen extSig name (var outmostFuelArg) $ rewrite lenEq in values, Just (_ ** extSig.gendOrder))

    -- get the expression of calling the internal gen, derive if necessary
    internalGenCall <- do

      -- look for existing (already derived) internals, use it if exists
      let Nothing = List.Map.lookup sig !get
        | Just name => pure $ callCanonic sig name fuel values

      -- nothing found, then derive! acquire the name
      let name = nameForGen sig

      -- remember that we're responsible for this signature derivation
      modify $ List.Map.insert sig name

      -- remember the task to derive
      modify {stateType=List _} $ (::) (sig, name)

      -- return the name of the newly derived generator
      pure $ callCanonic sig name fuel values

    -- if we were first to start the derivation loop, then...
    when startLoop $ do
      -- start the derivation loop itself
      deriveAll
      -- we now are not in charge of the derivation loop, so reset the flag
      put True

    -- call the internal gen
    logPoint DetailedDebug "deptycheck.derive.closuring.internal" [sig] "is used as an internal generator"
    pure (internalGenCall, Nothing)

    where

      deriveOne : (GenSignature, Name) -> m ()
      deriveOne (sig, name) = do

        -- derive declaration and body for the asked signature. It's important to call it AFTER update of the map in the state to not to cycle
        let genFunClaim = export' name $ canonicSig sig
        _ : NamesInfoInTypes <- get
        _ : ConsRecs <- get
        genFunBody <- logBounds Info "deptycheck.derive.type" [sig] $ def name <$> assert_total canonicBody sig name

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
runCanonic : DeriveBodyForType => NamesInfoInTypes => ConsRecs =>
             SortedMap ExternalGenSignature Name -> (forall m. DerivationClosure m => m a) -> Elab (a, List Decl)
runCanonic exts calc = do
  let exts = SortedMap.fromList $ exts.asList <&> \namedSig => (fst $ internalise $ fst namedSig, namedSig)
  (x, defs, bodies) <- evalRWST
                         exts
                         (empty, empty, empty, %search, %search, True)
                         calc
                         {s=(ListMap GenSignature Name, List (GenSignature, Name), SortedSet Name, NamesInfoInTypes, ConsRecs, _)}
                         {w=(_, _)}
  pure (x, defs ++ bodies)

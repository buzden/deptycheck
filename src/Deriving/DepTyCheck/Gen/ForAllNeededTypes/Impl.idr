||| A bridge between a single act of derivation (for a single type) and a user derivation task
module Deriving.DepTyCheck.Gen.ForAllNeededTypes.Impl

import public Control.Monad.Either
import public Control.Monad.Reader
import public Control.Monad.State
import public Control.Monad.State.Tuple
import public Control.Monad.Writer
import public Control.Monad.RWS

import public Data.DPair
import public Data.List.Ex
import public Data.List.Map
import public Data.SortedMap
import public Data.SortedMap.Extra
import public Data.SortedSet

import public Decidable.Equality

import public Deriving.DepTyCheck.Gen.ForOneType.Interface

import public Deriving.SpecialiseData
import public Language.Reflection.Unify

%default total

isSimpleN : Name -> Bool
isSimpleN (UN (Basic str)) = (fst $ span isLower str) /= ""
isSimpleN _ = False

||| Given an argument, a possible given value for it, and a set of free variable names in scope,
||| return argument value in the specialisation lambda body,
||| as well as a list of newly introduced free variables and their given values
processArg : Arg -> Maybe TTImp -> SortedSet Name -> (TTImp, List (Arg, Maybe TTImp))
processArg arg Nothing fvNames = (IVar EmptyFC $ fromMaybe "_" arg.name, [(arg, Nothing)])
processArg arg (Just given) fvNames =
  case snd $ unPi arg.type of
    `(Type) => do
      let simpleNames = filter isSimpleN $ allVarNames given
      let newNames = filter (not . contains' fvNames) simpleNames
      let newArgs : List (Arg, Maybe TTImp) = (\x => (MkArg MW ExplicitArg (Just x) `(_), Just $ IVar EmptyFC x)) <$> newNames
      (given, newArgs)
    _ => (IVar EmptyFC $ fromMaybe "_" arg.name, [(arg, Just given)])

processArgs' :
  List (Fin x, Arg) ->
  List (Fin x, TTImp) ->
  SnocList (Arg, Maybe TTImp) ->
  SortedSet Name ->
  (List AnyApp, SnocList (Arg, Maybe TTImp), SortedSet Name)
processArgs' [] _ fvArgs fvNames = ([], fvArgs, fvNames)
processArgs' ((argIdx, arg) :: xs) givens fvArgs fvNames = do
  let (givens, argVal, newFVs) : (List _, TTImp, List _) = case givens of
        [] => ([], processArg arg Nothing fvNames)
        ((givenIdx, givenVal) :: ys) =>
          if (givenIdx == argIdx)
            then (ys, processArg arg (Just givenVal) fvNames)
            else (givens, processArg arg Nothing fvNames)
  let newFVNames = SortedSet.fromList $ fromMaybe "_" . name . fst <$> newFVs
  let fvArgs = fvArgs <>< newFVs
  let fvNames = union fvNames newFVNames
  mapFst (appArg arg argVal ::) $ processArgs' xs givens fvArgs fvNames

processArgs :
  (sig : GenSignature) ->
  List (Fin sig.targetType.args.length, Arg) ->
  List (Fin sig.targetType.args.length, TTImp) ->
  (TTImp, List Arg, List $ Maybe TTImp)
processArgs sig args givens = do
  let (argVals, fvArgs, _) = processArgs' args givens [<] empty
  (reAppAny (IVar EmptyFC sig.targetType.name) argVals, unzip $ toList fvArgs)

remap : List (Maybe TTImp, Fin x, Arg) -> List (TTImp, Fin x, Arg)
remap [] = []
remap ((Nothing, _, _) :: xs) = remap xs
remap ((Just x, y, z) :: xs) = (x,y,z) :: remap xs

formGivenVals : Vect l _ -> List TTImp -> Vect l TTImp
formGivenVals [] _ = []
formGivenVals (_ :: xs) [] = (`(_) :: formGivenVals xs [])
formGivenVals (x :: xs) (y :: ys) = y :: formGivenVals xs ys

genSS : List (TTImp, Fin x, Arg) -> (s : SortedSet (Fin x) ** Vect s.size TTImp)
genSS l = do
  let (l1, l2) = unzip l
  let (l2, l3) = unzip l2
  let s = SortedSet.fromList l2
  let gv = formGivenVals (Vect.fromList $ Prelude.toList s) l1
  (s ** gv)

%tcinline
specialiseIfNeeded :
  Monad m =>
  Elaboration m =>
  NamesInfoInTypes =>
  DerivationClosure m =>
  (sig : GenSignature) ->
  (specTaskToName : TTImp -> Name) ->
  (fuel : TTImp) ->
  Vect sig.givenParams.size TTImp ->
  m $ Maybe (List Decl, TypeInfo, TTImp)
specialiseIfNeeded sig specTaskToName fuel givenParamValues = do
  let givenIdxVals = (Prelude.toList sig.givenParams) `zipV` givenParamValues
  -- Check if there are any given type args, if not return Nothing
  let True = any (\a => snd (unPi a.type) == `(Type)) $ index' sig.targetType.args <$> Prelude.toList sig.givenParams
    | False => pure Nothing
  let argsWithIdx = withIndex sig.targetType.args
  let (lambdaRet, fvArgs, givenSubst) = processArgs sig argsWithIdx givenIdxVals
  (lambdaTy, lambdaBody) <- normaliseTask fvArgs lambdaRet
  let specName = specTaskToName lambdaBody
  (specTy, specDecls) : (TypeInfo, List Decl) <- case lookupType specName of
    Nothing => do
      Right (specTy, specDecls) <- runEitherT {m} {e=SpecialisationError} $ specialiseDataRaw specName lambdaTy lambdaBody
      | Left err => fail "INTERNAL ERROR: Specialisation \{show lambdaBody} failed with error \{show err}."
      pure (specTy, specDecls)
    Just specTy => pure (specTy, [])
  let Yes stNamed = areAllTyArgsNamed specTy
  | No _ => fail "INTERNAL ERROR: Specialised type \{show specTy.name} does not have fully named arguments and constructors."
  let (newGP ** newGVals) = genSS $ remap $ zip givenSubst $ withIndex specTy.args
  (inv, cg_rhs) <- callGen (MkGenSignature specTy newGP) fuel newGVals
  let inv = case cg_rhs of
        Nothing => inv
        Just (n ** perm) => reorderGend False perm inv
  pure $ Just (specDecls, specTy, inv)


--- Particular implementations producing the-core-derivation-function closure ---

ClosuringContext : (Type -> Type) -> Type
ClosuringContext m =
  ( MonadReader (SortedMap GenSignature (ExternalGenSignature, Name)) m -- external gens
  , MonadState  (ListMap GenSignature Name) m                           -- gens already asked to be derived
  , MonadState  (List (GenSignature, Name)) m                           -- queue of gens to be derived
  , MonadState  (NamesInfoInTypes, ConsRecs) m                          -- current known types and their recursiveness and consturctor weights
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
    modify {stateType=SortedSet Name} $ insert ty.name
    _ : (NamesInfoInTypes, ConsRecs) <- get
    whenJust (deriveWeightingFun ty) $ tell . mapHom singleton

  callGen sig fuel values = do

    -- look for external gens, and call it if exists
    let Nothing = lookupLengthChecked sig !ask
      | Just (name, Element extSig lenEq) =>
          logValue Details "deptycheck.derive.closuring.external" [sig] "is used as an external generator" $
            (callExternalGen extSig name (var outmostFuelArg) $ rewrite lenEq in values, Just (_ ** extSig.gendOrder))

    -- check if we are the first, then we need to start the loop, and say that no one needs any more startups, we are in charge
    startLoop <- get <* put False

    -- update names info in types and cons recs if the asked type is not there
    _ <- considerNewType sig.targetType

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
    logValue DetailedDebug "deptycheck.derive.closuring.internal" [sig] "is used as an internal generator"
      (internalGenCall, Nothing)

    where

      considerNewType : TypeInfo -> m (NamesInfoInTypes, ConsRecs)
      considerNewType ty = do
        nc : (NamesInfoInTypes, ConsRecs) <- get
        let False = isTypeKnown ty | True => pure nc
        updateNamesAndConsRecs sig.targetType >>= \x => put x $> x

      deriveOne : (GenSignature, Name) -> m ()
      deriveOne (sig, name) = do

        -- derive declaration and body for the asked signature. It's important to call it AFTER update of the map in the state to not to cycle
        let genFunClaim = export' name $ canonicSig sig
        _ : (NamesInfoInTypes, ConsRecs) <- get
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
                         ((%search, %search), empty, empty, empty, True)
                         calc
                         {s=((NamesInfoInTypes, ConsRecs), ListMap GenSignature Name, List (GenSignature, Name), SortedSet Name, _)}
                         {w=(_, _)}
  pure (x, defs ++ bodies)

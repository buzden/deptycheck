||| A bridge between a single act of derivation and a user derivation task
module Test.DepTyCheck.Gen.Auto.Checked

import public Control.Monad.Either
import public Control.Monad.Reader
import public Control.Monad.State
import public Control.Monad.State.Tuple
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
    , MonadState  (SortedMap GenSignature Name) m -- gens already asked to be derived
    , MonadState  (SortedMap GenSignature AdditionalGens) m -- actual additional gens required for the gen
    , MonadWriter (List Decl, List Decl) m -- function declarations and bodies
    )

  -- Instead of staticly ensuring that map holds only correct values, we check dynamically, because it's hard to go through `==`-based lookup of maps.
  lookupLengthChecked : (intSig : GenSignature) -> SortedMap GenSignature (ExternalGenSignature, Name) ->
                        Maybe (Name, Subset ExternalGenSignature $ \extSig => extSig.givenParams.size = intSig.givenParams.size)
  lookupLengthChecked intSig m = lookup intSig m >>= \(extSig, name) => (name,) <$>
                                   case decEq extSig.givenParams.size intSig.givenParams.size of
                                      Yes prf => Just $ Element extSig prf
                                      No _    => Nothing

  DerivatorCore => ClojuringContext m => Elaboration m => CanonicGen m where
    callGen outerSig sig fuel values = do

      -- look for external gens, and call it if exists
      let Nothing = lookupLengthChecked sig !ask
        | Just (name, Element extSig lenEq) => pure (callExternalGen extSig name fuel $ rewrite lenEq in values, neutral)
                                               -- TODO to support non-trivial additional gens for external generators

      -- get the name of internal gen, derive if necessary
      (internalGenName, additionals) <- do

        -- manage if we were asked to call for polymorphic gen
        let False = isPolyType $ sig.targetType
          | True => pure (nameForGen sig, neutral)
                    -- TODO actually, there new additional gens should be created, not in particular cons derivator

        -- look for existing (already derived) internals, use it if exists
        let Nothing = SortedMap.lookup sig !get
          | Just name => do
              adds <- case SortedMap.lookup sig !get of
                        Nothing  => modify (insert sig $ the AdditionalGens neutral) $> neutral -- remember for future consistency check
                        Just ads => pure ads
              pure (name, adds)

        -- nothing found, then derive! acquire the name
        let name = nameForGen sig

        -- remember that we're responsible for this signature derivation
        modify $ insert sig name

        -- derive declaration and body for the asked signature. It's important to call it AFTER update of the map in the state to not to cycle
        (genFunClaim, genFunBody, additionals) <- assert_total $ deriveCanonical sig name

        -- remember the derived stuff
        tell ([genFunClaim], [genFunBody])

        -- check that so inconsistency in additional gens, i.e. that it was not used due to mutual recursion before generation
        case SortedMap.lookup sig !get of
          Nothing => pure ()
          Just savedAdds =>
            when (additionals /= savedAdds) $
              fail $ "Can't derive generator for \{show $ sig.targetType.name} because of polymorphic parameters AND mutual recursion"
                  ++ ", this combination is not supported yet"

        -- remember the additionals of the derived generator
        modify $ SortedMap.insert sig additionals

        -- return the name and additional generators of newly derived generator
        pure (name, additionals)

      -- form the basic expression to call the internal generator (required additional generators are not considered yet)
      let callExpr = callCanonic sig internalGenName fuel values

      -- prepare wrappers of the call that set additionals to the main gen call + form next-level additionals, if any
      (callWrappers, outerAdditionalsOfCall) <- runWriterT {m} $ for additionals.additionalGens.asList $
        \askedAdditionalSig => do

          -- get which given agrument corresponds to the asked additional signature
          let Just askedAdditionalPolyIdx =
                findIndex (\giv => (argName $ index' sig.targetType.args giv) == askedAdditionalSig.targetType.unpolyName) sig.givenParams.asList
            | Nothing => fail $ "INTERNAL ERROR: can't find asked additional signature `\{show askedAdditionalSig.targetType.name}`"
                             ++ " when calling for `\{show sig.targetType.name}` from `\{show outerSig.targetType.name}`"
                         -- TODO maybe, to manage universal generator here too, if `askedAdditionalSig` is in the `outerSig.targetType.args`,
                         --      but not in `outerSig.givenParams`.

          -- get which expression in the call is on the place of the current poly gen
          let exprForPolyType = index askedAdditionalPolyIdx values

          -- treat this expression as an application of (potentially) a type to an arguments
          let (subTyExpr, subTyArgs) = unAppAny exprForPolyType

          -- check if what's all applied to is actually a type and acquire a `TypeInfo`
          ti <- case subTyExpr of -- TODO check of this form is present at least three times throughout the code, simplify it
                  IVar fc nm         => getInfo' nm
                                  `try` (if null subTyArgs
                                           then pure $ typeInfoForPolyType nm []
                                           else failAt fc "Higher-order polymorphic types are not supported yet")
                                        -- TODO to think what if this parameter is a not present in the context
                  IPrimVal _ (PrT t) => pure $ typeInfoForPrimType t
                  IType _            => pure $ typeInfoForTypeOfTypes
                  expr               => failAt (getFC expr) "Given expression must be a name of a type"

          -- form a derivation task for generation of this type
          let subsig = MkGenSignature ti $ fromList $ toList $ allFins' {n=ti.args.length}

          -- decide the name for the small fuel argument
          let subfuel = "add^fuel"

          -- check that we can deal with actual arguments of the type being called for
          subTyArgs <- for subTyArgs $ \case
            PosApp exp     => pure exp
            NamedApp n exp => failAt (getFC exp) "Implicit arguments are not supported yet"
            AutoApp exp    => failAt (getFC exp) "Auto arguments application is not supported"
            WithApp exp    => failAt (getFC exp) "With arguments application is not supported"

          -- align the lengths of actual and expected arguments
          let Yes lengthCorrect = subsig.givenParams.size `decEq` subTyArgs.length
            | No _ => fail "INTERNAL ERROR: lengths of actual and expected arg lists in application of `\{show sig.targetType.name}` do not match"
          let subTyArgs = Vect.fromList subTyArgs

          -- form a generator call expression
          (addCallExpr, addAdds) <- assert_total $ callGen outerSig subsig (var subfuel) $ rewrite lengthCorrect in subTyArgs

          -- remember recursive additionals, if any
          tell addAdds

          -- form a generator substitution expression
          pure $ \exp => autoApp exp $ lambdaArg subfuel .=> addCallExpr

      -- apply all wrappers that add additional generators to the call expression
      let callExpr = foldl (\exp, wr => wr exp) callExpr callWrappers

      -- remember the need for the universal generator
      let outerAdditionalsOfCall = {universalGen $= (|| additionals.universalGen)} outerAdditionalsOfCall

      -- call the internal gen
      pure (callExpr, outerAdditionalsOfCall)

  --- Canonic-dischagring function ---

  export
  runCanonic : DerivatorCore => SortedMap ExternalGenSignature Name -> (forall m. CanonicGen m => m a) -> Elab (a, List Decl)
  runCanonic exts calc = do
    let exts = SortedMap.fromList $ exts.asList <&> \namedSig => (fst $ internalise $ fst namedSig, namedSig)
    (x, defs, bodies) <- evalRWST exts (empty, empty) calc {s=(SortedMap GenSignature Name, SortedMap GenSignature AdditionalGens)} {w=(_, _)}
    pure (x, defs ++ bodies)

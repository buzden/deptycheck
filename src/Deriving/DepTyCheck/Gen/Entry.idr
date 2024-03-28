||| Derivation interface for an end-point user
module Deriving.DepTyCheck.Gen.Entry

import public Data.Fuel

import public Decidable.Equality

import public Deriving.DepTyCheck.Gen.Checked
import public Deriving.DepTyCheck.Gen.Core

import public Test.DepTyCheck.Gen -- for `Gen` data type

%default total

----------------------------------------
--- Internal functions and instances ---
----------------------------------------

--- Info of code position ---

record GenSignatureFC where
  constructor MkGenSignatureFC
  sigFC        : FC
  genFC        : FC
  targetTypeFC : FC

--- Collection of external `Gen`s ---

record GenExternals where
  constructor MkGenExternals
  externals : List (ExternalGenSignature, TTImp)

--- Info for distinguishing signature checking context ---

data GenCheckSide
  = DerivationTask
  | ExternalGen

isDerivationTask : GenCheckSide -> Bool
isDerivationTask DerivationTask = True
isDerivationTask _              = False

isExternalGen : GenCheckSide -> Bool
isExternalGen ExternalGen = True
isExternalGen _           = False

OriginalSignatureInfo : ExternalGenSignature -> GenExternals -> Type
OriginalSignatureInfo sig exts = SortedSet $ Fin $ sig.givenParams.size + exts.externals.length

CheckResult : GenCheckSide -> Type
CheckResult DerivationTask = (sig : ExternalGenSignature ** exts : GenExternals ** OriginalSignatureInfo sig exts)
CheckResult ExternalGen    = (GenSignatureFC, ExternalGenSignature)

--- Analysis functions ---

checkTypeIsGen : (checkSide : GenCheckSide) -> TTImp -> Elab $ CheckResult checkSide
checkTypeIsGen checkSide sig = do

  -- check the given expression is a type
  _ <- check {expected=Type} sig

  -- treat the given type expression as a (possibly 0-ary) function type
  (sigArgs, sigResult) <- unPiNamed sig

  -----------------------------------------
  -- First checks in the given arguments --
  -----------------------------------------

  -- check that there are at least some parameters in the signature
  let (firstArg::sigArgs) = sigArgs
    | [] => failAt (getFC sig) "No arguments in the generator function signature, at least a fuel argument must be present"

  -- check that the first argument an explicit unnamed one
  let MkArg MW ExplicitArg (MN _ _) (IVar firstArgFC firstArgTypeName) = firstArg
    | _ => failAt (getFC firstArg.type) "The first argument must be explicit, unnamed, present at runtime and of type `Fuel`"

  -- check the type of the fuel argument
  unless !(firstArgTypeName `isSameTypeAs` `{Data.Fuel.Fuel}) $
    failAt firstArgFC "The first argument must be of type `Fuel`"

  ---------------------------------------------------------------
  -- First looks at the resulting type of a generator function --
  ---------------------------------------------------------------

  -- check the resulting type is `Gen`
  let IApp _ (IApp _ (IVar genFC topmostResultName) (IVar _ genEmptiness)) targetType = sigResult
    | _ => failAt (getFC sigResult) "The result type of the generator function must be of type \"`Gen MaybeEmpty` of desired result\""

  unless !(topmostResultName `isSameTypeAs` `{Test.DepTyCheck.Gen.Gen}) $
    failAt (getFC sigResult) "The result type of the generator function must be of type \"`Gen MaybeEmpty` of desired result\""

  unless (genEmptiness `nameConformsTo` `{Test.DepTyCheck.Gen.Emptiness.MaybeEmpty}) $
    failAt genFC "Only `GenBeEmptyStatic` variant of generator is supported, `\{show genEmptiness}` is given"
    -- this check can be changed to `==` as soon as we gen the result type normalised properly.

  -- treat the generated type as a dependent pair
  let Just (paramsToBeGenerated, targetType) = unDPairUnAlt targetType
    | Nothing => failAt (getFC targetType) "Unable to interpret type under `Gen` as a dependent pair"

  -- remember the right target type position
  let targetTypeFC = getFC targetType

  -- treat the target type as a function application
  let (targetType, targetTypeArgs) = unAppAny targetType

  -- check out applications types
  targetTypeArgs <- for targetTypeArgs $ \case
    PosApp     arg => pure arg
    NamedApp n arg => failAt targetTypeFC "Target types with implicit type parameters are not supported yet"
    AutoApp    arg => failAt targetTypeFC "Target types with `auto` implicit type parameters are not supported yet"
    WithApp    arg => failAt targetTypeFC "Unexpected `with`-application in the target type"

  ------------------------------------------
  -- Working with the target type familly --
  ------------------------------------------

  -- acquire `TypeInfo` out of the target type `TTImp` expression
  targetType <- case targetType of

    -- Normal type
    IVar _ targetType => getInfo' targetType <|> failAt genFC "Target type `\{show targetType}` is not a top-level data definition"

    -- Primitive type
    IPrimVal _ (PrT t) => pure $ typeInfoForPrimType t

    -- Type of types
    IType _ => pure typeInfoForTypeOfTypes

    _ => failAt targetTypeFC "Target type is not a simple name"

  --------------------------------------------------
  -- Target type family's arguments' first checks --
  --------------------------------------------------

  -- check all the arguments of the target type are variable names, not complex expressions
  targetTypeArgs <- for targetTypeArgs $ \case
    IVar _ (UN argName) => pure argName
    nonVarArg => failAt (getFC nonVarArg) "Target type's argument must be a variable name"

  -- check that all arguments names are unique
  let [] = findDiffPairWhich (==) targetTypeArgs
    | _ :: _ => failAt targetTypeFC "All arguments of the target type must be different"

  -- check the given type info corresponds to the given type application, and convert a `List` to an appropriate `Vect`
  let Yes targetTypeArgsLengthCorrect = targetType.args.length `decEq` targetTypeArgs.length
    | No _ => fail "INTERNAL ERROR: unequal argument lists lengths: \{show targetTypeArgs.length} and \{show targetType.args.length}"

  ------------------------------------------------------------
  -- Parse `Reflect` structures to what's needed to further --
  ------------------------------------------------------------

  -- check that all parameters of `DPair` are as expected
  paramsToBeGenerated <- for paramsToBeGenerated $ \case
    MkArg MW ExplicitArg (Just $ UN nm) t => pure (nm, t)
    _                                     => failAt (getFC sigResult) "Argument of dependent pair under the resulting `Gen` must be named"

  -- check that all arguments are omega, not erased or linear; and that all arguments are properly named
  (givenParams, autoImplArgs, givenParamsPositions) <- do
    let
      classifyArg : forall m. Elaboration m =>
                    NamedArg -> m $ Either (ArgExplicitness, UserName, TTImp) TTImp
      classifyArg $ MkArg MW ImplicitArg (UN name) type = pure $ Left (Checked.ImplicitArg, name, type)
      classifyArg $ MkArg MW ExplicitArg (UN name) type = pure $ Left (Checked.ExplicitArg, name, type)
      classifyArg $ MkArg MW AutoImplicit (MN _ _) type = pure $ Right type

      classifyArg $ MkArg MW ImplicitArg     _ ty = failAt (getFC ty) "Implicit argument must be named and must not shadow any other name"
      classifyArg $ MkArg MW ExplicitArg     _ ty = failAt (getFC ty) "Explicit argument must be named and must not shadow any other name"
      classifyArg $ MkArg MW AutoImplicit    _ ty = failAt (getFC ty) "Auto-implicit argument must be unnamed"

      classifyArg $ MkArg M0 _               _ ty = failAt (getFC ty) "Erased arguments are not supported in generator function signatures"
      classifyArg $ MkArg M1 _               _ ty = failAt (getFC ty) "Linear arguments are not supported in generator function signatures"
      classifyArg $ MkArg MW (DefImplicit _) _ ty = failAt (getFC ty) "Default implicit arguments are not supported in generator function signatures"

    map partitionEithersPos $ for sigArgs.asVect classifyArg

  ----------------------------------------------------------------------
  -- Check that generated and given parameter lists are actually sets --
  ----------------------------------------------------------------------

  -- check that all parameters in `parametersToBeGenerated` have different names
  let [] = findDiffPairWhich ((==) `on` fst) paramsToBeGenerated
    | (_, (_, ty)) :: _ => failAt (getFC ty) "Name of the argument is not unique in the dependent pair under the resulting `Gen`"

  -- check that all given parameters have different names
  let [] = findDiffPairWhich ((==) `on` \(_, n, _) => n) givenParams
    | (_, (_, _, ty)) :: _ => failAt (getFC ty) "Name of the generator function's argument is not unique"

  -----------------------------------------------------------------------
  -- Link generated and given parameters lists to the `targetTypeArgs` --
  -----------------------------------------------------------------------

  -- check that all parameters to be generated are actually used inside the target type
  paramsToBeGenerated <- for {b=(_, Fin targetType.args.length)} paramsToBeGenerated $ \(name, ty) => case findIndex (== name) targetTypeArgs of
    Just found => pure (ty, rewrite targetTypeArgsLengthCorrect in found)
    Nothing => failAt (getFC ty) "Generated parameter is not used in the target type"

  -- check that all target type's parameters classied as "given" are present in the given params list
  givenParams <- for {b=(_, Fin targetType.args.length, _)} givenParams $ \(explicitness, name, ty) => case findIndex (== name) targetTypeArgs of
    Just found => pure (ty, rewrite targetTypeArgsLengthCorrect in found, explicitness, UN name)
    Nothing => failAt (getFC ty) "Given parameter is not used in the target type"

  -- check the increasing order of generated params
  let [] = findConsequentsWhich ((>=) `on` snd) paramsToBeGenerated
    | (_, (ty, _)) :: _ => failAt (getFC ty) "Generated arguments must go in the same order as in the target type"

  -- check the increasing order of given params
  let [] = findConsequentsWhich ((>=) `on` \(_, n, _) => n) givenParams
    | (_, (ty, _, _)) :: _ => failAt (getFC ty) "Given arguments must go in the same order as in the target type"

  -- make unable to use generated params list
  let 0 paramsToBeGenerated = paramsToBeGenerated

  -- forget the order of the given params, convert to a map from index to explicitness
  let givenParams = fromList $ snd <$> givenParams

  -- make the resulting signature
  let genSig = MkExternalGenSignature {targetType, givenParams}

  -------------------------------------
  -- Auto-implicit generators checks --
  -------------------------------------

  -- check that external gen does not have its own external gens
  when (isExternalGen checkSide) $
    when (not $ null autoImplArgs) $
      failAt genFC "Auto-implicit argument should not contain its own auto-implicit arguments"

  -- check all auto-implicit arguments pass the checks for the `Gen` in an appropriate context
  autoImplArgs <- for autoImplArgs $ \tti => mapSnd (,tti) <$> checkTypeIsGen ExternalGen (assert_smaller sig tti)

  -- check that all auto-imlicit arguments are unique
  let [] = findDiffPairWhich ((==) `on` \(_, sig, _) => sig) autoImplArgs
    | (_, (fc, _)) :: _ => failAt fc.targetTypeFC "Repetition of an auto-implicit external generator"

  -- check that the resulting generator is not in externals
  let Nothing = find ((== genSig) . \(_, sig, _) => sig) autoImplArgs
    | Just (fc, _) => failAt fc.genFC "External generators contain the generator asked to be derived"

  -- forget FCs of subparsed externals
  let autoImplArgs = snd <$> autoImplArgs

  ------------
  -- Result --
  ------------

  case checkSide of
    DerivationTask => do
      let Yes prf = genSig.givenParams.size + autoImplArgs.length `decEq` sigArgs.length
        | No _ => fail $ "INTERNAL ERROR: positions length is incorrect"
                      ++ ", \{show sigArgs.length} is not \{show genSig.givenParams.size} + \{show autoImplArgs.length}"
      pure (genSig ** MkGenExternals autoImplArgs ** rewrite prf in givenParamsPositions)
    ExternalGen    => do
      let fc = MkGenSignatureFC {sigFC=getFC sig, genFC, targetTypeFC}
      pure (fc, genSig)

--- Boundaries between external and internal generator functions ---

nameForGen : ExternalGenSignature -> Name
nameForGen sig = let (ty, givs) = characteristics sig in UN $ Basic $ "external^<\{ty}>\{show givs}"
-- I'm using `UN` but containing chars that cannot be present in the code parsed from the Idris frontend.

-- this is a workarond for Idris compiler bug #2983
nameMod : Name -> Name
nameMod n = UN $ Basic "outer^<\{show n}>"

internalGenCallingLambda : Elaboration m => CheckResult DerivationTask -> TTImp -> m TTImp
internalGenCallingLambda (sig ** exts ** givsPos) call = do
    let Just args = joinEithersPos sig.givenParams.asList exts.externals givsPos
      | Nothing => fail "INTERNAL ERROR: can't join partitioned args back"
    pure $ foldr mkLam call args

  where

  -- either given param or auto param
  mkLam : Either (Fin sig.targetType.args.length, ArgExplicitness, Name) (ExternalGenSignature, TTImp) -> TTImp -> TTImp
  mkLam $ Left (idx, expl, name) = lam $ MkArg MW expl.toTT .| Just (nameMod name) .| implicitTrue -- (index' sig.targetType.args idx).type
                                                                                   -- ^^^ no type because of `nameMod` above
  mkLam $ Right (extSig, ty)     = lam $ MkArg MW AutoImplicit .| Just (nameForGen extSig) .| ty
                                   -- TODO to think whether it's okay to calculate the name twice: here and below for a map

callMainDerivedGen : CanonicGen m => ExternalGenSignature -> (fuelArg : Name) -> m TTImp
callMainDerivedGen sig fuelArg =
  let Element intSig prf = internalise sig in
  callGen intSig (var fuelArg) $ rewrite prf in sig.givenParams.asVect <&> \(_, _, name) => var $ nameMod name

wrapFuel : (fuelArg : Name) -> TTImp -> TTImp
wrapFuel fuelArg = lam $ MkArg MW ExplicitArg (Just fuelArg) `(Data.Fuel.Fuel)

------------------------------
--- Functions for the user ---
------------------------------

export
deriveGenExpr : DerivatorCore => (signature : TTImp) -> Elab TTImp
deriveGenExpr signature = do
  checkResult@(signature ** externals ** _) <- checkTypeIsGen DerivationTask signature
  let externalsSigToName = fromList $ externals.externals <&> \(sig, _) => (sig, nameForGen sig)
  let fuelArg = outmostFuelArg
  niit <- logBounds "namesInfo" [] $ getNamesInfoInTypes signature.targetType
  (callExpr, locals) <- runCanonic externalsSigToName $ callMainDerivedGen signature fuelArg
  wrapFuel fuelArg <$> internalGenCallingLambda checkResult (local locals callExpr)

||| The entry-point function of automatic derivation of `Gen`'s.
|||
||| Consider, you have a `data X (a : A) (b : B n) (c : C) where ...` and
||| you want a derived `Gen` for `X`.
||| Say, you want to have `a` and `c` parameters of `X` to be set by the caller and the `b` parameter to be generated.
||| For this your generator function should have a signature like `(a : A) -> (c : C) -> (n ** b : B n ** X a b c)`.
||| So, you need to define a function with this signature, say, named as `genX` and
||| to write `genX = deriveGen` as an implementation to make the body to be derived.
|||
||| Say, you want `n` to be set by the caller and, as the same time, to be an implicit argument.
||| In this case, the signature of the main function to be derived,
||| becomes `{n : _} -> (a : A) -> (c : C) -> (b : B n ** X a b c)`.
||| But still, you can use this function `deriveGen` to derive a function with such signature.
|||
||| Say, you want your generator to be parameterized with some external `Gen`'s.
||| Consider types `data Y where ...`, `data Z1 where ...` and `data Z2 (b : B n) where ...`.
||| For this, `auto`-parameters can be listed with `=>`-syntax in the signature.
|||
||| For example, if you want to use `Gen Y` and `Gen`'s for `Z1` and `Z2` as external generators,
||| you can define your function in the following way:
|||
|||   ```idris
|||   genX : Gen Y => Gen Z1 => ({n : _} -> {b : B n} -> Gen (Z2 b)) => {n : _} -> (a : A) -> (c : C) -> Gen (b : B n ** X a b c)
|||   genX = deriveGen
|||   ```
|||
||| Consider also, that you may be asked for having the `Fuel` argument as the first argument in the signature
||| due to (maybe, temporary) unability of `Gen`'s to manage infinite processes of values generation.
||| So, the example from above will look like this:
|||
|||   ```idris
|||   genX : Fuel -> (Fuel -> Gen Y) => (Fuel -> Gen Z1) => (Fuel -> {n : _} -> {b : B n} -> Gen (Z2 b)) =>
|||          {n : _} -> (a : A) -> (c : C) -> Gen (b : B n ** X a b c)
|||   genX = deriveGen
|||   ```
|||
|||
export %macro
deriveGen : DerivatorCore => Elab a
deriveGen = do
  Just signature <- goal
     | Nothing => fail "The goal signature is not found. Generators derivation must be used only for fully defined signatures"
  tt <- deriveGenExpr signature
  check tt

||| Alternative entry-point function of automatic derivation of `Gen`'s.
|||
||| This function can be used precisely as the `deriveGen`.
||| The only difference is that this function does not rely on somewhat fragile goal mechanism
||| allowing the user to pass the desired type explicitly.
|||
||| Since Idris allows simple top-level definitions to not to contain type signature,
||| one can use this derivation function as a one-liner without repetition of a desired type, e.g.
|||
|||   ```idris
|||   genX = deriveGenFor $ Fuel -> (Fuel -> Gen Y) => (a : A) -> (c : C) -> Gen (b ** X a b c)
|||   ```
export %macro
deriveGenFor : DerivatorCore => (0 a : Type) -> Elab a
deriveGenFor a = do
  sig <- quote a
  tt <- deriveGenExpr sig
  check tt

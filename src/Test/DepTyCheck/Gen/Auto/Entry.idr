||| External generation interface and aux stuff for that
module Test.DepTyCheck.Gen.Auto.Entry

import Data.Either
import public Data.Fuel

import public Test.DepTyCheck.Gen -- for `Gen` data type
import public Test.DepTyCheck.Gen.Auto.Checked

%default total

-------------------------
--- Utility functions ---
-------------------------

listToVectExact : (n : Nat) -> List a -> Maybe $ Vect n a
listToVectExact Z     []      = Just []
listToVectExact (S k) (x::xs) = (x ::) <$> listToVectExact k xs
listToVectExact Z     (_::_)  = Nothing
listToVectExact (S k) []      = Nothing

-----------------------------------------
--- Utility `TTImp`-related functions ---
-----------------------------------------

--- Parsing `TTImp` stuff ---

unDPair : TTImp -> (List (Count, PiInfo TTImp, Maybe Name, TTImp), TTImp)
unDPair (IApp _ (IApp _ (IVar _ `{Builtin.DPair.DPair}) typ) (ILam _ cnt piInfo mbname _ lamTy)) =
    mapFst ((cnt, piInfo, mbname, typ)::) $ unDPair lamTy
unDPair expr = ([], expr)

--- Pretty-printing ---

Show TTImp where
  show expr = show $ assert_total {- WTF?? Why do I need it here? -} $ pretty {ann=Unit} expr

----------------------------------------
--- Internal functions and instances ---
----------------------------------------

analyzeSigResult : TTImp -> Elab (List (Name, TTImp), (ty : TypeInfo ** Vect ty.args.length Name))
analyzeSigResult sigResult = do
  -- check the resulting type is `Gen`
  let IApp _ (IVar _ `{Test.DepTyCheck.Gen.Gen}) targetType = sigResult
    | _ => fail "The result type must be a `deptycheck`'s `Gen` applied to a type"

  -- treat the generated type as a dependent pair
  let (paramsToBeGenerated, targetType) = unDPair targetType

  -- check that all parameters of `DPair` are as expected
  paramsToBeGenerated <- for paramsToBeGenerated $ \case
    (MW, ExplicitArg, Just nm, t) => pure (nm, t)
    (_,  _,           Nothing, _) => fail "All arguments of dependent pair under the resulting `Gen` are expected to be named"
    _                             => fail "Bad lambda argument of RHS of dependent pair under the resulting `Gen`, it must be `MW` and explicit"

  -- treat the target type as a function application and check it's applied to some name
  let (IVar _ targetType, targetTypeArgs) = unApp targetType
    | _ => fail "Target type is not a simple name: \{show targetType}"

  -- check that desired `Gen` is not a generator of `Gen`s
  case targetType of
    `{Test.DepTyCheck.Gen.Gen} => fail "Target type of a derived `Gen` cannot be a `deptycheck`'s `Gen`"
    _ => pure ()

  -- check we can analyze the target type itself
  targetType <- getInfo' targetType

  -- check that there are at least non-zero constructors
  let (_::_) = targetType.cons
    | [] => fail "No constructors found for the type `\{show targetType.name}`"

  -- check the given type info corresponds to the given type application, and convert a `List` to an appropriate `Vect`
  let Just targetTypeArgs = listToVectExact targetType.args.length targetTypeArgs
    | Nothing => fail "Lengths of target type applcation and description are not equal: \{show targetTypeArgs.length} and \{show targetType.args.length}"

  -- check all the arguments of the target type are variable names, not complex expressions
  targetTypeArgs <- for targetTypeArgs $ \case
    IVar _ argName => pure argName
    nonVarArg => fail "All arguments of the resulting `\{show targetType.name}` are expected to be variable names, but `\{show nonVarArg}` is not"

  pure (paramsToBeGenerated, (targetType ** targetTypeArgs))

-- This function either fails or not instead of returning some error-containing result.
-- This is due to technical limitation of the `Elab`'s `check` function.
-- TODO To think of return type of `TypeInfo` and, maybe, somewhat parsed arguments,
--      like `Vect ty.args.length $ Maybe ArgExplicitness`, like is was before.
-- TODO Also, maybe, there is a need in the result of some map from `TypeInfo` (and, maybe, `Vect` like above) to `auto-implicit | hinted`.
--      Or, at least, the filled generators manager, that remembers what already is generated (and how it is named) and
--      what is present as external (with auto-implicit or hinted).
--      In this case, it would be a stateful something.
checkTypeIsGen : TTImp -> Elab ()
checkTypeIsGen sig = do
  -- check the given expression is a type
  _ <- check {expected=Type} sig

  -- treat the given type expression as a (possibly 0-ary) function type
  let (sigArgs, sigResult) = unPi sig

--  logMsg "gen.derive" 0 $ "goal's result:\n- \{show sigResult}"

  -- check and parse the resulting part of the generator function's signature
  (paramsToBeGenerated, (targetType ** targetTypeArgs)) <- analyzeSigResult sigResult

  let (MkArg MW ImplicitArg (Just `{fuel}) (IVar _ `{Data.Fuel.Fuel}))::sigArgs = sigArgs
    | _ => fail "The first argument in a generator's function signature must be `{fuel : Fuel}`"

  -- check that all arguments are omega, not erased or linear; and that all arguments are properly named
  let notSupported : Maybe Name -> (cntType : String) -> String
      notSupported name cntType = "\{cntType} arguments are not supported in generator signatures, "
                               ++ maybe "an unnamed one" (\name => "`\{show name}`") name ++ " is such"
  sigArgs <- for {b = Either _ TTImp} sigArgs $ \case
    MkArg M0 _               name    _  => fail $ notSupported name "Erased"
    MkArg M1 _               name    _  => fail $ notSupported name "Linear"
    MkArg MW (DefImplicit _) name    _  => fail $ notSupported name "Default implicit"
    MkArg MW ImplicitArg     Nothing _  => fail "All implicit arguments are expected to be named"
    MkArg MW ExplicitArg     Nothing _  => fail "All explicit arguments are expected to be named"
    MkArg MW AutoImplicit (Just name) _ => fail "Named auto-implicit parameters are not expected, in particular `\{show name}`"
    MkArg MW ImplicitArg (Just name) type => pure $ Left (Checked.ImplicitArg, name, type)
    MkArg MW ExplicitArg (Just name) type => pure $ Left (Checked.ExplicitArg, name, type)
    MkArg MW AutoImplicit Nothing    type => pure $ Right type
  let (givenParams, autoImplArgs) = (lefts sigArgs, rights sigArgs) -- `partitionEithers sigArgs` does not reduce here somewhy :-(

  -- TODO to check whether all target type's argument names are present either in the function's arguments or in the resulting generated depedent pair.

  ?checkTypeIsGen_impl

  -- result
  --   check the resulting type is `Gen`
  --   check the `Gen`'s parameter is pure type or a dependent pair resulting a pure type
  --   check that all parts of the dependent pair are the type parameters of the target type
  --   (not sure, if needed) check that parameters of the target type are open (either a parameter of function or present in the dependent pair)
  -- arguments
  --   check all arguments are MW, not M0 or M1
  --   check the first explicit argument is `Fuel`
  --   (not sure, if needed) check all `auto` `implicit` external `Gen`'s are before the all other parameters
  --   (not sure, if needed) check that all arguments are actually used
  -- externals
  --   check there are no repetition in the external gens lists, both in auto-implicit and hinted, and also between them
  --

------------------------------
--- Functions for the user ---
------------------------------

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
||| Some of these `Gen`'s are known declared `%hint x : Gen Y`, some of them should go as an `auto` parameters.
||| Consider types `data Y where ...`, `data Z1 where ...` and `data Z2 (b : B n) where ...`.
||| For this, `auto`-parameters can be listed with `=>`-syntax in the signature.
||| External generators declared with `%hint` need to be listed separately in the implicit argument of `deriveGen`.
|||
||| For example, if you want to use `%hint` for `Gen Y` and `Gen`'s for `Z1` and `Z2` to be `auto` parameters,
||| you can define your function in the following way:
|||
|||   ```idris
|||   genX : Gen Z1 => ({n : _} -> {b : B n} -> Gen (Z2 b)) => {n : _} -> (a : A) -> (c : C) -> (b : B n ** X a b c)
|||   genX = deriveGen { externalHintedGens = [ `(Gen Y) ] }
|||   ```
|||
||| `%hint _ : Gen Y` from the current scope will be used as soon as a value of type `Y` will be needed for generation.
|||
||| Consider another example, where all generators for `Y`, `Z1` and `Z2` are means to be defined with `%hint`.
||| In this case, you are meant to declare it in the following way:
|||
|||   ```idris
|||   genX : {n : _} -> (a : A) -> (c : C) -> (b : B n ** X a b c)
|||   genX = deriveGen { externalHintedGens = [ `(Gen Z1), `({n : _} -> {b : B n} -> Gen (Z2 b)), `(Gen Y) ] }
|||   ```
|||
||| Consider also, that you may be asked for having the `Fuel` argument as the first argument in the signature
||| due to (maybe, temporary) unability of `Gen`'s to manage infinite processes of values generation.
|||
export %macro
deriveGen : {default [] externalHintedGens : List TTImp} -> Elab a
deriveGen = do
  Just signature <- goal
     | Nothing => fail "The goal signature is not found. Generators derivation must be used only for fully defined signatures"
  checkTypeIsGen signature
  for_ externalHintedGens checkTypeIsGen
  ?deriveGen_foo

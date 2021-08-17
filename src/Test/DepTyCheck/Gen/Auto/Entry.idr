||| External generation interface and aux stuff for that
module Test.DepTyCheck.Gen.Auto.Entry

import public Data.Either
import public Data.Fuel

import public Debug.Reflection

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

-- Finds leftmost pair that gives `True` on the given relation
findLeftmostPair : (a -> a -> Bool) -> List a -> Maybe (a, a)
findLeftmostPair _   []      = Nothing
findLeftmostPair rel (x::xs) = (x, ) <$> find (rel x) xs <|> findLeftmostPair rel xs

-----------------------------------------
--- Utility `TTImp`-related functions ---
-----------------------------------------

--- Parsing `TTImp` stuff ---

unDPair : TTImp -> (List (Count, PiInfo TTImp, Maybe Name, TTImp), TTImp)
unDPair (IApp _ (IApp _ (IVar _ `{Builtin.DPair.DPair}) typ) (ILam _ cnt piInfo mbname _ lamTy)) =
    mapFst ((cnt, piInfo, mbname, typ)::) $ unDPair lamTy
unDPair expr = ([], expr)

--- General purpose instances ---

Eq Namespace where
  MkNS xs == MkNS ys = xs == ys

Eq Name where
  UN x   == UN y   = x == y
  MN x n == MN y m = x == y && n == m
  NS s n == NS p m = s == p && n == m
  DN x n == DN y m = x == y && n == m
  RF x   == RF y   = x == y
  _ == _ = False

----------------------------------------
--- Internal functions and instances ---
----------------------------------------

data UserDefinedName = UserName String

Eq UserDefinedName where
  (==) = (==) `on` \(UserName n) => n

record GenSignature where
  constructor MkGenSignature
  sigFC        : FC
  genFC        : FC
  targetTypeFC : FC

  targetType : TypeInfo
  targetTypeArgs : Vect targetType.args.length UserDefinedName

  -- non-checked, but meant to be that these two do not intersect and their union is a full set
  paramsToBeGenerated : List $ Fin targetType.args.length
  givenParams         : List $ Fin targetType.args.length

record GenInfraSignature where
  constructor MkGenInfraSignature
  sig : GenSignature
  autoImplExternals : List GenSignature
  hintedExternals   : List GenSignature

isSameTypeAs : Name -> Name -> Elab Bool
isSameTypeAs checked expected = [| getInfo' checked `eq` getInfo' expected |] where
  eq : TypeInfo -> TypeInfo -> Bool
  eq = (==) `on` name

checkTypeIsGen : (hinted : List TTImp) -> TTImp -> Elab GenInfraSignature
checkTypeIsGen hinted sig = do

  -- check the given expression is a type
  _ <- check {expected=Type} sig

  -- treat the given type expression as a (possibly 0-ary) function type
  (sigArgs, sigResult) <- unPiNamed sig

  -----------------------------------------
  -- First checks in the given arguments --
  -----------------------------------------

  -- check that there are at least some parameters in the signature
  let (firstArg::sigArgs) = sigArgs
    | [] => failAt (getFC sig) "No arguments in the signature, at least a fuel argument must be present"

  -- check that the first argument an explicit unnamed one
  let MkArg MW ExplicitArg (MN _ _) (IVar firstArgFC firstArgTypeName) = firstArg
    | _ => failAt (getFC firstArg.type) "The first argument must be an explicit unnamed runtime one of type `Fuel`"

  -- check the type of the fuel argument
  unless !(firstArgTypeName `isSameTypeAs` `{Data.Fuel.Fuel}) $
    failAt firstArgFC "The first argument must be of type `Fuel`"

  ---------------------------------------------------------------
  -- First looks at the resulting type of a generator function --
  ---------------------------------------------------------------

  -- check the resulting type is `Gen`
  let IApp _ (IVar genFC topmostResultName) targetType = sigResult
    | _ => failAt (getFC sigResult) "The result type must be a `deptycheck`'s `Gen` applied to a type"

  unless !(topmostResultName `isSameTypeAs` `{Test.DepTyCheck.Gen.Gen}) $
    failAt (getFC sigResult) "The result type must be a `deptycheck`'s `Gen` applied to a type"

  -- treat the generated type as a dependent pair
  let (paramsToBeGenerated, targetType) = unDPair targetType

  -- treat the target type as a function application
  let (targetType, targetTypeArgs) = unApp targetType

  ------------------------------------------
  -- Working with the target type familly --
  ------------------------------------------

  -- check it's applied to some name
  let IVar targetTypeFC targetType = targetType
    | _ => failAt (getFC targetType) "Target type is not a simple name"

  -- check that desired `Gen` is not a generator of `Gen`s
  when !(targetType `isSameTypeAs` `{Test.DepTyCheck.Gen.Gen}) $
    failAt targetTypeFC "Target type of a derived `Gen` cannot be a `deptycheck`'s `Gen`"

  -- check we can analyze the target type itself
  targetType <- getInfo' targetType

  -- check that there are at least non-zero constructors
  let (_::_) = targetType.cons
    | [] => fail "No constructors found for the type `\{show targetType.name}`"

  --------------------------------------------------
  -- Target type family's arguments' first checks --
  --------------------------------------------------

  -- check the given type info corresponds to the given type application, and convert a `List` to an appropriate `Vect`
  let Just targetTypeArgs = listToVectExact targetType.args.length targetTypeArgs
    | Nothing => fail "Lengths of target type applcation and description are not equal: \{show targetTypeArgs.length} and \{show targetType.args.length}"

  -- check all the arguments of the target type are variable names, not complex expressions
  targetTypeArgs <- for targetTypeArgs $ \case
    IVar _ (UN argName) => pure $ UserName argName
    nonVarArg => failAt (getFC nonVarArg) "Argument is expected to be a variable name"

  ------------------------------------------------------------
  -- Parse `Reflect` structures to what's needed to further --
  ------------------------------------------------------------

  -- check that all parameters of `DPair` are as expected
  paramsToBeGenerated <- for paramsToBeGenerated $ \case
    (MW, ExplicitArg, Just (UN nm), t) => pure (UserName nm, t)
    (_,  _,           _           , _) => failAt (getFC sigResult) "All arguments of dependent pair under the resulting `Gen` are expected to be named"
    _                                  => failAt (getFC sigResult) "Bad lambda argument of RHS of dependent pair under the `Gen`, it must be `MW` and explicit"

  -- check that all arguments are omega, not erased or linear; and that all arguments are properly named
  sigArgs <- for {b = Either _ TTImp} sigArgs $ \case
    MkArg MW ImplicitArg (UN name) type => pure $ Left (Checked.ImplicitArg, UserName name, type)
    MkArg MW ExplicitArg (UN name) type => pure $ Left (Checked.ExplicitArg, UserName name, type)
    MkArg MW AutoImplicit (MN _ _) type => pure $ Right type

    MkArg MW ImplicitArg     _ ty => failAt (getFC ty) "Implicit arguments are expected to be named"
    MkArg MW ExplicitArg     _ ty => failAt (getFC ty) "Explicit arguments are expected to be named"
    MkArg MW AutoImplicit    _ ty => failAt (getFC ty) "Auto-implicit arguments are expected to be unnamed"

    MkArg M0 _               _ ty => failAt (getFC ty) "Erased arguments are not supported in generator signatures"
    MkArg M1 _               _ ty => failAt (getFC ty) "Linear arguments are not supported in generator signatures"
    MkArg MW (DefImplicit _) _ ty => failAt (getFC ty) "Default implicit arguments are not supported in generator signatures"
  let givenParams := lefts sigArgs
  let autoImplArgs := rights sigArgs
  --let (givenParams, autoImplArgs) := (lefts sigArgs, rights sigArgs) -- `partitionEithers sigArgs` does not reduce here somewhy :-(

  ----------------------------------------------------------------------
  -- Check that generated and given parameter lists are actually sets --
  ----------------------------------------------------------------------

  -- check that all parameters in `parametersToBeGenerated` have different names
  let Nothing = findLeftmostPair ((==) `on` fst) paramsToBeGenerated
    | Just (_, (_, ty)) => failAt (getFC ty) "Name of the argument is not unique in the dependent pair"

  -- check that all given parameters have different names
  let Nothing = findLeftmostPair ((==) `on` (Builtin.fst . snd)) givenParams
    | Just (_, (_, _, ty)) => failAt (getFC ty) "Name of the argument is not unique"

  -----------------------------------------------------------------------
  -- Link generated and given parameters lists to the `targetTypeArgs` --
  -----------------------------------------------------------------------

  -- check that all parameters to be generated are actually used inside the target type
  paramsToBeGenerated <- for paramsToBeGenerated $ \(name, ty) => case elemIndex name targetTypeArgs of
    Just found => pure found
    Nothing => failAt (getFC ty) "Generated parameter is not used in the target type"

  -- check that all target type's parameters classied as "given" are present in the given params list
  givenParams <- for givenParams $ \(explicitness, name, ty) => case elemIndex name targetTypeArgs of
    Just found => pure found
    Nothing => failAt (getFC ty) "Given parameter is not used in the target type"

  ------------------------------------------------
  -- Auto-implicit and hinted generators checks --
  ------------------------------------------------

  -- check all auto-implicit arguments pass the checks for the `Gen` and do not contain their own auto-implicits
  autoImplArgs <- subCheck "Auto-implicit" autoImplArgs

  -- check all hinted arguments pass the checks for the `Gen`
  hinted <- subCheck "Hinted" hinted

  ------------
  -- Result --
  ------------

  pure $ MkGenInfraSignature
           (MkGenSignature {sigFC=getFC sig, genFC, targetTypeFC, targetType, targetTypeArgs, paramsToBeGenerated, givenParams})
           autoImplArgs
           hinted

  where
    subCheck : (desc : String) -> List TTImp -> Elab $ List GenSignature
    subCheck desc = traverse $ checkTypeIsGen [] >=> \case
      MkGenInfraSignature {sig=s, autoImplExternals=[], hintedExternals=[]} => pure s
      MkGenInfraSignature {sig=s, autoImplExternals=_::_, _} => failAt s.genFC "\{desc} argument should not contain its own auto-implicit arguments"
      MkGenInfraSignature {sig=s, hintedExternals=_::_, _} => failAt s.genFC "INTERNAL ERROR: parsed hinted externals are unexpectedly non empty"

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
  _ <- checkTypeIsGen externalHintedGens signature
  ?deriveGen_foo

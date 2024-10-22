||| Several tactics for derivation of particular generators for a constructor regarding to how they use externals
module Deriving.DepTyCheck.Gen.Core.ConsDerive

import public Control.Monad.State

import public Data.Collections.Analysis
import public Data.Either
import public Data.Fin.Map
import public Data.SortedSet.Extra

import public Decidable.Equality

import public Deriving.DepTyCheck.Gen.Derive

%default total

record Determination (0 con : Con) where
  constructor MkDetermination
  ||| Args which cannot be determined by this arg, e.g. because it is used in a non-trivial expression.
  stronglyDeterminingArgs : SortedSet $ Fin con.args.length
  ||| Args which this args depends on, which are not strongly determining.
  argsDependsOn : SortedSet $ Fin con.args.length
  ||| Count of type arguments of the type of this arguments
  typeArgs : Nat

record TypeApp (0 con : Con) where
  constructor MkTypeApp
  argHeadType : TypeInfo
  {auto 0 argHeadTypeGood : AllTyArgsNamed argHeadType}
  argApps : Vect argHeadType.args.length .| Either (Fin con.args.length) TTImp
  determ  : Determination con

getTypeApps : Elaboration m => NamesInfoInTypes => (con : Con) -> m $ Vect con.args.length $ TypeApp con
getTypeApps con = do
  let conArgIdxs = SortedMap.fromList $ mapI con.args $ \idx, arg => (argName arg, idx)

  -- Analyse that we can do subgeneration for each constructor argument
  -- Fails using `Elaboration` if the given expression is not an application to a type constructor
  let analyseTypeApp : TTImp -> m $ TypeApp con
      analyseTypeApp expr = do
        let (lhs, args) = unAppAny expr
        ty <- case lhs of
          IVar _ lhsName     => do let Nothing = lookupType lhsName -- TODO to support `lhsName` to be a type parameter of type `Type`
                                     | Just found => pure found
                                   -- we didn't found, failing, there are at least two reasons
                                   failAt (getFC lhs) $ if isNamespaced lhsName
                                     then "Data type `\{lhsName}` is unavailable at the site of derivation (forgotten import?)"
                                     else "Usupported applications to a non-concrete type `\{lhsName}`"
          IPrimVal _ (PrT t) => pure $ typeInfoForPrimType t
          IType _            => pure typeInfoForTypeOfTypes
          lhs@(IPi {})       => failAt (getFC lhs) "Fields with function types are not supported in constructors"
          lhs                => failAt (getFC lhs) "Unsupported type of a constructor field: \{show lhs}"
        let Yes lengthCorrect = decEq ty.args.length args.length
          | No _ => failAt (getFC lhs) "INTERNAL ERROR: wrong count of unapp when analysing type application"
        _ <- ensureTyArgsNamed ty
        let as = rewrite lengthCorrect in args.asVect <&> \arg => case getExpr arg of
                   expr@(IVar _ n) => mirror . maybeToEither expr $ lookup n conArgIdxs
                   expr            => Right expr
        let stronglyDeterminedBy = fromList $ mapMaybe (lookup' conArgIdxs) $ rights as.asList >>= allVarNames
        let argsDependsOn = fromList (lefts as.asList) `difference` stronglyDeterminedBy
        pure $ MkTypeApp ty as $ MkDetermination stronglyDeterminedBy argsDependsOn ty.args.length

  for con.args.asVect $ analyseTypeApp . type

-------------------------------------------------
--- Derivation of a generator for constructor ---
-------------------------------------------------

--- Interface ---

public export
interface ConstructorDerivator where
  consGenExpr : CanonicGen m => GenSignature -> (con : Con) -> (given : SortedSet $ Fin con.args.length) -> (fuel : TTImp) -> m TTImp

  ||| Workarond of inability to put an arbitrary name under `IBindVar`
  bindNameRenamer : Name -> String
  bindNameRenamer $ UN $ Basic n = n
  bindNameRenamer n = "^bnd^" ++ show n

--- Particular tactics ---

mapDetermination : {0 con : Con} -> (SortedSet (Fin con.args.length) -> SortedSet (Fin con.args.length)) -> Determination con -> Determination con
mapDetermination f = {stronglyDeterminingArgs $= f, argsDependsOn $= f}

removeDeeply : Foldable f =>
               (toRemove : f $ Fin con.args.length) ->
               (fromWhat : FinMap con.args.length $ Determination con) ->
               FinMap con.args.length $ Determination con
removeDeeply toRemove fromWhat = foldl delete' fromWhat toRemove <&> mapDetermination (\s => foldl delete' s toRemove)

propagatePriOnce : Ord p => FinMap con.args.length (Determination con, p) -> FinMap con.args.length (Determination con, p)
propagatePriOnce =
  -- propagate back along dependencies
  (\dets => map (\(det, pri) => (det,) $ foldl (\x => maybe x (max x . snd) . lookup' dets) pri $ det.argsDependsOn) dets)
  .
  -- propagate back along strong determinations
  (\dets => foldl (\dets, (det, pri) => foldl (flip $ updateExisting $ map $ max pri) dets det.stronglyDeterminingArgs) dets dets)

propagatePri : Ord p => FinMap con.args.length (Determination con, p) -> FinMap con.args.length (Determination con, p)
propagatePri dets = do
  let next = propagatePriOnce dets
  if ((==) `on` map snd) dets next
    then dets
    else assert_total propagatePri next

findFirstMax : Ord p => List (a, b, p) -> Maybe (a, b)
findFirstMax [] = Nothing
findFirstMax ((x, y, pri)::xs) = Just $ go (x, y) pri xs where
  go : (a, b) -> p -> List (a, b, p) -> (a, b)
  go curr _       []                = curr
  go curr currPri ((x, y, pri)::xs) = if pri > currPri then go (x, y) pri xs else go curr currPri xs

searchOrder : {con : _} ->
              (determinable : SortedSet $ Fin con.args.length) ->
              (left : FinMap con.args.length $ Determination con) ->
              List $ Fin con.args.length
searchOrder determinable left = do

  -- compute the priority
  -- priority is a count of given arguments, and it propagates back using `max` on strongly determining arguments and on arguments that depend on this
  let leftWithPri = propagatePri $ left <&> \det => (det,) $ det.typeArgs `minus` det.argsDependsOn.size

  -- find all arguments that are not stongly determined by anyone, among them find all that are not determined even weakly, if any
  let notDetermined = filter (\(idx, det, _) => not (contains idx determinable) && null det.stronglyDeterminingArgs) $ kvList leftWithPri

  -- choose the one from the variants
  -- It's important to do so, since after discharging one of the selected variable, set of available variants can extend
  -- (e.g. because of discharging of strong determination), and new alternative have more priority than current ones.
  -- TODO to determine the best among current variants taking into account which indices are more complex (transitively!)
  let Just (curr, currDet) = findFirstMax notDetermined
    | Nothing => []

  -- remove information about all currently chosen args
  let next = removeDeeply .| Id curr .| removeDeeply currDet.argsDependsOn left

  -- `next` is smaller than `left` because `curr` must be not empty
  curr :: searchOrder (determinable `difference` currDet.argsDependsOn) (assert_smaller left next)

||| "Non-obligatory" means that some present external generator of some type
||| may be ignored even if its type is really used in a generated data constructor.
namespace NonObligatoryExts

  ||| Least-effort non-obligatory tactic is one which *does not use externals* during taking a decision on the order.
  ||| It uses externals if decided order happens to be given by an external generator, but is not obliged to use any.
  ||| It is seemingly most simple to implement, maybe the fastest and
  ||| fits well when external generators are provided for non-dependent types.
  export
  [LeastEffort] {default False simplificationHack : Bool} -> ConstructorDerivator where
    consGenExpr sig con givs fuel = do

      -- Prepare local search context
      let _ : NamesInfoInTypes = %search    -- I don't why it won't be found without this

      -------------------------------------------------------------
      -- Prepare intermediate data and functions using this data --
      -------------------------------------------------------------

      -- Compute left-to-right need of generation when there are non-trivial types at the left
      argsTypeApps <- getTypeApps con

      -- Get arguments which any other argument depends on
      let dependees = dependees con.args

      -- Decide how constructor arguments would be named during generation
      let bindNames = withIndex (fromList con.args) <&> map (bindNameRenamer . argName)

      -- Form the expression of calling the current constructor
      let callCons = do
        let constructorCall = callCon con $ bindNames <&> \(idx, n) => if contains idx dependees then implicitTrue else varStr n
        let wrapImpls : Nat -> TTImp
            wrapImpls Z     = constructorCall
            wrapImpls (S n) = var `{Builtin.DPair.MkDPair} .$ implicitTrue .$ wrapImpls n
        let consExpr = wrapImpls $ sig.targetType.args.length `minus` sig.givenParams.size
        `(Prelude.pure {f=Test.DepTyCheck.Gen.Gen _} ~consExpr)

      -- Derive constructor calling expression for given order of generation
      let genForOrder : List (Fin con.args.length) -> m TTImp
          -- ... state is the set of arguments that are already present (given or generated)
          genForOrder order = map (foldr apply callCons) $ evalStateT givs $ for order $ \genedArg => do

            -- Get info for the `genedArg`
            let MkTypeApp typeOfGened argsOfTypeOfGened _ = index genedArg $ the (Vect _ $ TypeApp con) argsTypeApps

            -- Acquire the set of arguments that are already present
            presentArguments <- get

            -- TODO to put the following check as up as possible as soon as it typecheks O_O
            -- Check that those argument that we need to generate is not already present
            let False = contains genedArg presentArguments
              | True => pure id

            -- Filter arguments classification according to the set of arguments that are left to be generated;
            -- Those which are `Right` are given, those which are `Left` are needs to be generated.
            let depArgs : Vect typeOfGened.args.length (Either (Fin con.args.length) TTImp) := argsOfTypeOfGened <&> \case
              Right expr => Right expr
              Left i     => if contains i presentArguments then Right $ var $ argName $ index' con.args i else Left i

            -- Determine which arguments will be on the left of dpair in subgen call, in correct order
            let subgeneratedArgs = mapMaybe getLeft $ toList depArgs

            -- Make sure generated arguments will not be generated again
            modify $ insert genedArg . union (fromList subgeneratedArgs)

            -- Form a task for subgen
            let (subgivensLength ** subgivens) = mapMaybe (\(ie, idx) => (idx,) <$> getRight ie) $ depArgs `zip` Fin.range
            let subsig : GenSignature := MkGenSignature typeOfGened $ fromList $ fst <$> toList subgivens
            let Yes Refl = decEq subsig.givenParams.size subgivensLength
              | No _ => fail "INTERNAL ERROR: error in given params set length computation"

            -- Check if called subgenerator can call the current one
            let mutRec = hasNameInsideDeep sig.targetType.name $ var subsig.targetType.name

            -- Decide whether to use local (decreasing) or outmost fuel, depending on whether we are in mutual recursion with subgen
            let subfuel = if mutRec then fuel else var outmostFuelArg

            -- Form an expression to call the subgen
            subgenCall <- callGen subsig subfuel $ snd <$> subgivens

            -- Form an expression of binding the result of subgen
            let genedArg:::subgeneratedArgs = genedArg:::subgeneratedArgs <&> bindVar . snd . flip Vect.index bindNames
            let bindSubgenResult = foldr (\l, r => var `{Builtin.DPair.MkDPair} .$ l .$ r) genedArg subgeneratedArgs

            -- Form an expression of the RHS of a bind; simplify lambda if subgeneration result type does not require pattern matching
            let bindRHS = \cont => case bindSubgenResult of
                                     IBindVar _ n => lam (MkArg MW ExplicitArg (Just $ UN $ Basic n) implicitFalse) cont
                                     _            => `(\ ~bindSubgenResult => ~cont)

            -- Chain the subgen call with a given continuation
            pure $ \cont => `(~subgenCall >>= ~(bindRHS cont))

      --------------------------------------------
      -- Compute possible orders of generation ---
      --------------------------------------------

      -- Compute determination map without weak determination information
      let determ = insertFrom' empty $ mapI (\i, ta => (i, ta.determ)) argsTypeApps

      logPoint {level=15} "least-effort" [sig, con] "- determ: \{determ}"
      logPoint {level=15} "least-effort" [sig, con] "- givs: \{givs}"

      let nonDetermGivs = removeDeeply givs determ
      let theOrder = searchOrder (concatMap argsDependsOn nonDetermGivs) nonDetermGivs

      logPoint {level=10} "least-effort" [sig, con] "- used final order: \{theOrder}"

      --------------------------
      -- Producing the result --
      --------------------------

      with FromString.(.label)
      labelGen "\{show con.name} (orders)".label <$> genForOrder theOrder

      where

        Interpolation (Fin con.args.length) where
          interpolate i = case name $ index' con.args i of
            Just (UN n) => "#\{show i} (\{show n})"
            _           => "#\{show i}"

        Foldable f => Interpolation (f $ Fin con.args.length) where
          interpolate = ("[" ++) . (++ "]") . joinBy ", " . map interpolate . toList

        Interpolation (Determination con) where
          interpolate ta = "<=\{ta.stronglyDeterminingArgs} ->\{ta.argsDependsOn}"

  ||| Best effort non-obligatory tactic tries to use as much external generators as possible
  ||| but discards some there is a conflict between them.
  ||| All possible non-conflicting layouts may be produced in the generated values list.
  |||
  ||| E.g. when we have external generators ``(a : _) -> (b : T ** C a b)`` and ``(b : T ** D b)`` and
  ||| a constructor of form ``C a b -> D b -> ...``, we can use values from both pairs
  ||| ``(a : _) -> (b : T ** C a b)`` with ``(b : T) -> D b`` and
  ||| ``(a : _) -> (b : T) -> C a b`` with ``(b : T ** D b)``,
  ||| i.e. to use both of external generators to form the generated values list
  ||| but not obligatorily all the external generators at the same time.
  export
  [BestEffort] ConstructorDerivator where
    consGenExpr sig con givs fuel = do
      ?cons_body_besteff_nonoblig_rhs

||| "Obligatory" means that is some external generator is present and a constructor has
||| an argument of a type which is generated by this external generator, it must be used
||| in the constructor's generator.
|||
||| Dependent types are important here, i.e. generator ``(a : _) -> (b ** C a b)``
||| is considered to be a generator for the type ``C``.
||| The problem with obligatory generators is that some external generators may be incompatible.
|||
|||   E.g. once we have ``(a : _) -> (b ** C a b)`` and ``(a ** b ** C a b)`` at the same time,
|||   once ``C`` is used in the same constructor, we cannot guarantee that we will use both external generators.
|||
|||   The same problem is present once we have external generators for ``(a : _) -> (b : T ** C a b)`` and ``(b : T ** D b)`` at the same time,
|||   and both ``C`` and ``D`` are used in the same constructor with the same parameter of type ``T``,
|||   i.e. when constructor have something like ``C a b -> D b -> ...``.
|||
|||   Notice, that this problem does not arise in constructors of type ``C a b1 -> D b2 -> ...``
|||
||| In this case, we cannot decide in general which value of type ``T`` to be used for generation is we have to use both generators.
||| We can either fail to generate a value for such constructor (``FailFast`` tactic),
||| or alternatively we can try to match all the generated values of type ``T`` from both generators
||| using ``DecEq`` and leave only intersection (``DecEqConflicts`` tactic).
namespace ObligatoryExts

  export
  [FailFast] ConstructorDerivator where
    consGenExpr sig con givs fuel = do
      ?cons_body_obl_ff_rhs

  export
  [DecEqConflicts] ConstructorDerivator where
    consGenExpr sig con givs fuel = do
      ?cons_body_obl_deceq_rhs

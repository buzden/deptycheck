||| Several tactics for derivation of particular generators for a constructor regarding to how they use externals
module Deriving.DepTyCheck.Gen.ForOneTypeConRhs.Impl

import public Control.Monad.State
import public Control.Monad.State.Tuple

import public Data.Collections.Analysis
import public Data.Either
import public Data.Fin.Map
import public Data.SortedSet.Extra
import public Data.Vect.Extra

import public Decidable.Equality

import public Deriving.DepTyCheck.Gen.ForOneTypeConRhs.Interface
import public Deriving.DepTyCheck.Gen.Labels
import public Deriving.DepTyCheck.Gen.Tuning

%default total

-------------------------------------------------------------------
--- Data types characterising constructors for particular tasks ---
-------------------------------------------------------------------

record Determination (0 con : Con) where
  constructor MkDetermination
  ||| Args which cannot be determined by this arg, e.g. because it is used in a non-trivial expression.
  stronglyDeterminingArgs : SortedSet $ Fin con.args.length
  ||| Args which this args depends on, which are not strongly determining.
  argsDependsOn : SortedSet $ Fin con.args.length
  ||| Count of influencing arguments
  influencingArgs : Nat

mapDetermination : {0 con : Con} -> (SortedSet (Fin con.args.length) -> SortedSet (Fin con.args.length)) -> Determination con -> Determination con
mapDetermination f oldDet = do
  let newDet : Determination con := {stronglyDeterminingArgs $= f, argsDependsOn $= f} oldDet
  let patchInfl = if null (newDet.stronglyDeterminingArgs) && not (null oldDet.stronglyDeterminingArgs) then S else id
  ({influencingArgs $= patchInfl} newDet)

removeDeeply : Foldable f =>
               (toRemove : f $ Fin con.args.length) ->
               (fromWhat : FinMap con.args.length $ Determination con) ->
               FinMap con.args.length $ Determination con
removeDeeply toRemove fromWhat = foldl delete' fromWhat toRemove <&> mapDetermination (\s => foldl delete' s toRemove)

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
                                   -- we haven't found, failing, there are at least two reasons
                                   failAt (getFC lhs) $ if isNamespaced lhsName
                                     then "Data type `\{lhsName}` is unavailable at the site of derivation (forgotten import?)"
                                     else "Usupported applications to a non-concrete type `\{lhsName}` in \{show con.name}"
          IPrimVal _ (PrT t) => pure $ typeInfoForPrimType t
          IType _            => pure typeInfoForTypeOfTypes
          lhs@(IPi {})       => failAt (getFC lhs) "Fields with function types are not supported in constructors, like in \{show con.name}"
          lhs                => failAt (getFC lhs) "Unsupported type of a constructor's \{show con.name} field: \{show lhs}"
        let Yes lengthCorrect = decEq ty.args.length args.length
          | No _ => failAt (getFC lhs) "INTERNAL ERROR: wrong count of unapp when analysing type application"
        _ <- ensureTyArgsNamed ty
        let as = rewrite lengthCorrect in args.asVect <&> \arg => case getExpr arg of
                   expr@(IVar _ n) => mirror . maybeToEither expr $ lookup n conArgIdxs
                   expr            => Right expr
        let strongDetermination = rights as.asList <&> mapMaybe (lookup' conArgIdxs) . allVarNames
        let strongDeterminationWeight = concatMap @{Additive} (max 1 . length) strongDetermination -- we add 1 for constant givens
        let stronglyDeterminedBy = fromList $ join strongDetermination
        let argsDependsOn = fromList (lefts as.asList) `difference` stronglyDeterminedBy
        pure $ MkTypeApp ty as $ MkDetermination stronglyDeterminedBy argsDependsOn $ argsDependsOn.size + strongDeterminationWeight

  for con.args.asVect $ analyseTypeApp . type

----------------------------------------------------------------
--- Facilities for automatic search of good generation order ---
----------------------------------------------------------------

-- adds base priorities of args which we depend on transitively
refineBasePri : Num p => {con : _} -> FinMap con.args.length (Determination con, p) -> FinMap con.args.length (Determination con, p)
refineBasePri ps = snd $ execState (SortedSet.empty {k=Fin con.args.length}, ps) $ traverse_ go $ List.allFins _ where
  go : (visited : MonadState (SortedSet $ Fin con.args.length) m) =>
       (pris : MonadState (FinMap con.args.length (Determination con, p)) m) =>
       Monad m =>
       Fin con.args.length ->
       m ()
  go curr = do

    visited <- get
    -- if we already managed the current item, then exit
    let False = contains curr visited | True => pure ()
    -- remember that we are in charge of the current item
    let visited = insert curr visited
    put visited

    let Just (det, currPri) = lookup curr !(get @{pris}) | Nothing => pure ()

    let unvisitedDeps = det.argsDependsOn `union` det.stronglyDeterminingArgs

    -- run this for all dependences
    for_ (unvisitedDeps `difference` visited) $ assert_total go

    -- compute what needs to be added to the current priority
    let addition = mapMaybe (map snd . lookup' !(get @{pris})) (Prelude.toList unvisitedDeps)
    let newPri = foldl (+) currPri addition

    -- update the priority of the currenly managed argument
    modify $ updateExisting (mapSnd $ const newPri) curr

propagateStrongDet, propagateDep : Ord a => FinMap con.args.length (Determination con, a) -> FinMap con.args.length (Determination con, a)
-- propagate back along dependencies, but influence of this propagation should be approx. anti-propotrional to givens, hence `minus`
propagateDep dets = dets <&> \(det, pri) => (det,) $ foldl (\x => maybe x (max x . snd) . lookup' dets) pri $ det.argsDependsOn
-- propagate back along strong determinations
propagateStrongDet dets =
  foldl (\dets, (det, pri) => foldl (flip $ updateExisting $ map $ max pri) dets det.stronglyDeterminingArgs) dets dets

propagatePri : Ord a => FinMap con.args.length (Determination con, a) -> FinMap con.args.length (Determination con, a)
propagatePri dets = do
  let next = propagatePriOnce dets
  if ((==) `on` map snd) dets next
    then dets
    else assert_total propagatePri next
  where
    propagatePriOnce : FinMap con.args.length (Determination con, a) -> FinMap con.args.length (Determination con, a)
    propagatePriOnce = propagateDep . propagateStrongDet

data PriorityOrigin = Original | Propagated

Eq PriorityOrigin where
  Original   == Original   = True
  Propagated == Propagated = True
  _ == _ = False

Ord PriorityOrigin where
  compare Original   Original   = EQ
  compare Original   Propagated = GT
  compare Propagated Original   = LT
  compare Propagated Propagated = EQ

-- compute the priority
-- priority is a count of given arguments, and it propagates back using `max` on strongly determining arguments and on arguments that depend on this
-- additionally we take into account the number of outgoing strong determinations and count of dependent arguments
assignPriorities : {con : _} -> FinMap con.args.length (Determination con) -> FinMap con.args.length (Determination con, Nat, PriorityOrigin, Nat)
assignPriorities dets = do
  let invStrongDetPwr = do
    let _ : Monoid Nat = Additive
    flip concatMap dets $ \det => fromList $ (,1) <$> det.stronglyDeterminingArgs.asList
  -- the original priority is the count of already determined given arguments for each argument
  let origPri = refineBasePri $ dets <&> \det => (det,) $ det.influencingArgs `minus` det.argsDependsOn.size
  Fin.Map.mapWithKey' .| map snd origPri `zip` propagatePri origPri .| \idx, (origPri, det, newPri) =>
    (det, newPri, if origPri == newPri then Original else Propagated, fromMaybe 0 (Fin.Map.lookup idx invStrongDetPwr) + det.argsDependsOn.size)

findFirstMax : Ord p => List (a, b, p) -> Maybe (a, b)
findFirstMax [] = Nothing
findFirstMax ((x, y, pri)::xs) = Just $ go (x, y) pri xs where
  go : (a, b) -> p -> List (a, b, p) -> (a, b)
  go curr _       []                = curr
  go curr currPri ((x, y, pri)::xs) = if pri > currPri then go (x, y) pri xs else go curr currPri xs

searchOrder : {con : _} ->
              (left : FinMap con.args.length $ Determination con) ->
              List $ Fin con.args.length
searchOrder left = do

  -- find all arguments that are not stongly determined by anyone, among them find all that are not determined even weakly, if any
  let notDetermined = filter (\(idx, det, _) => null det.stronglyDeterminingArgs) $ kvList $ assignPriorities left

  -- choose the one from the variants
  -- It's important to do so, since after discharging one of the selected variable, set of available variants can extend
  -- (e.g. because of discharging of strong determination), and new alternative have more priority than current ones.
  -- TODO to determine the best among current variants taking into account which indices are more complex (transitively!)
  let Just (curr, currDet) = findFirstMax notDetermined
    | Nothing => []

  -- remove information about all currently chosen args
  let next = removeDeeply .| Id curr .| removeDeeply currDet.argsDependsOn left

  -- `next` is smaller than `left` because `curr` must be not empty
  curr :: searchOrder (assert_smaller left next)

callCon : (con : Con) -> Vect con.args.length TTImp -> TTImp
callCon con = reAppAny (var con.name) . toList . mapI (appArg . index' con.args)

---------------------------------------------------------------------------
---------------------------------------------------------------------------
--- Derivation of a generator for constructor's RHS, particular tactics ---
---------------------------------------------------------------------------
---------------------------------------------------------------------------

------------------------------
--- Non-obligatory tactics ---
------------------------------

-- "Non-obligatory" means that some present external generator of some type
-- may be ignored even if its type is really used in a generated data constructor.

||| Least-effort non-obligatory tactic is one which *does not use externals* during taking a decision on the order.
||| It uses externals if decided order happens to be given by an external generator, but is not obliged to use any.
||| It is seemingly most simple to implement, maybe the fastest and
||| fits well when external generators are provided for non-dependent types.
export
[LeastEffort] DeriveBodyRhsForCon where
  consGenExpr sig con givs fuel = do

    -- Prepare local search context
    let _ : NamesInfoInTypes = %search    -- I don't why it won't be found without this

    -------------------------------------------------------------
    -- Prepare intermediate data and functions using this data --
    -------------------------------------------------------------

    -- Compute left-to-right need of generation when there are non-trivial types at the left
    argsTypeApps <- getTypeApps con

    -- Decide how constructor arguments would be named during generation
    let bindNames = argName <$> fromList con.args

    -- Get arguments which any other argument depends on
    let dependees = dependees con.args

    -- Form the expression of calling the current constructor
    let callCons = do
      let constructorCall = callCon con $ bindNames.withIdx <&> \(idx, n) => if contains idx dependees then implicitTrue else var n
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
            Left i     => if contains i presentArguments then Right $ var $ index i bindNames else Left i

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
          (subgenCall, reordering) <- callGen subsig subfuel $ snd <$> subgivens

          -- Form an expression of binding the result of subgen
          let genedArg:::subgeneratedArgs = genedArg:::subgeneratedArgs <&> bindVar . flip Vect.index bindNames
          let Just subgeneratedArgs = reorder'' reordering subgeneratedArgs
            | Nothing => fail "INTERNAL ERROR: cannot reorder subgenerated arguments"
          let bindSubgenResult = foldr (\l, r => var `{Builtin.DPair.MkDPair} .$ l .$ r) genedArg subgeneratedArgs

          -- Form an expression of the RHS of a bind; simplify lambda if subgeneration result type does not require pattern matching
          let bindRHS = \cont => case bindSubgenResult of
                                   IBindVar _ n => lam (MkArg MW ExplicitArg (Just n) implicitFalse) cont
                                   _            => `(\ ~bindSubgenResult => ~cont)

          -- Chain the subgen call with a given continuation
          pure $ \cont => `(~subgenCall >>= ~(bindRHS cont))

    --------------------------------------------
    -- Compute possible orders of generation ---
    --------------------------------------------

    -- Compute determination map without weak determination information
    let determ = insertFrom' empty $ mapI (\i, ta => (i, ta.determ)) argsTypeApps

    logPoint {level=Debug} "deptycheck.derive.least-effort" [sig, con] "- determ: \{determ}"
    logPoint {level=Debug} "deptycheck.derive.least-effort" [sig, con] "- givs: \{givs}"

    -- Find user-imposed tuning of the order
    userImposed <- findUserImposedDeriveFirst

    -- Compute the order
    let nonDetermGivs = removeDeeply userImposed $ removeDeeply givs determ
    let theOrder = userImposed ++ searchOrder nonDetermGivs

    logPoint {level=FineDetails} "deptycheck.derive.least-effort" [sig, con] "- used final order: \{theOrder}"

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

      findUserImposedDeriveFirst : m $ List $ Fin con.args.length
      findUserImposedDeriveFirst = do
        Just impl <- search $ GenOrderTuning $ Con.name con | Nothing => pure []
        let Yes tyLen = decEq (isConstructor @{impl}).fst.typeInfo.args.length sig.targetType.args.length
          | No _ => fail "INTERNAL ERROR: type args length of found gen order tuning is wrong"
        let Yes conLen = decEq (isConstructor @{impl}).fst.conInfo.args.length con.args.length
          | No _ => fail "INTERNAL ERROR: con args length of found gen order tuning is wrong"
        -- TODO to get rid of `believe_me` below
        let df = believe_me $ deriveFirst @{impl} (rewrite tyLen in Prelude.toList sig.givenParams) (rewrite conLen in Prelude.toList givs)
        let userImposed = filter (not . contains' givs) $ nub $ conArgIdx <$> df
        logPoint {level=FineDetails} "deptycheck.derive.least-effort" [sig, con] "- user-imposed: \{userImposed}"
        pure userImposed

--||| Best effort non-obligatory tactic tries to use as much external generators as possible
--||| but discards some there is a conflict between them.
--||| All possible non-conflicting layouts may be produced in the generated values list.
--|||
--||| E.g. when we have external generators ``(a : _) -> (b : T ** C a b)`` and ``(b : T ** D b)`` and
--||| a constructor of form ``C a b -> D b -> ...``, we can use values from both pairs
--||| ``(a : _) -> (b : T ** C a b)`` with ``(b : T) -> D b`` and
--||| ``(a : _) -> (b : T) -> C a b`` with ``(b : T ** D b)``,
--||| i.e. to use both of external generators to form the generated values list
--||| but not obligatorily all the external generators at the same time.
--export
--[BestEffort] DeriveBodyRhsForCon where
--  consGenExpr sig con givs fuel = do
--    ?cons_body_besteff_nonoblig_rhs

--------------------------
--- Obligatory tactics ---
--------------------------

-- "Obligatory" means that is some external generator is present and a constructor has
-- an argument of a type which is generated by this external generator, it must be used
-- in the constructor's generator.
--
-- Dependent types are important here, i.e. generator ``(a : _) -> (b ** C a b)``
-- is considered to be a generator for the type ``C``.
-- The problem with obligatory generators is that some external generators may be incompatible.
--
--   E.g. once we have ``(a : _) -> (b ** C a b)`` and ``(a ** b ** C a b)`` at the same time,
--   once ``C`` is used in the same constructor, we cannot guarantee that we will use both external generators.
--
--   The same problem is present once we have external generators for ``(a : _) -> (b : T ** C a b)`` and ``(b : T ** D b)`` at the same time,
--   and both ``C`` and ``D`` are used in the same constructor with the same parameter of type ``T``,
--   i.e. when constructor have something like ``C a b -> D b -> ...``.
--
--   Notice, that this problem does not arise in constructors of type ``C a b1 -> D b2 -> ...``
--
-- In this case, we cannot decide in general which value of type ``T`` to be used for generation is we have to use both generators.
-- We can either fail to generate a value for such constructor (``FailFast`` tactic),
-- or alternatively we can try to match all the generated values of type ``T`` from both generators
-- using ``DecEq`` and leave only intersection (``DecEqConflicts`` tactic).

--export
--[FailFast] DeriveBodyRhsForCon where
--  consGenExpr sig con givs fuel = do
--    ?cons_body_obl_ff_rhs

--export
--[DecEqConflicts] DeriveBodyRhsForCon where
--  consGenExpr sig con givs fuel = do
--    ?cons_body_obl_deceq_rhs

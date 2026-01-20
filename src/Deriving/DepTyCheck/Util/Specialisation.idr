module Deriving.DepTyCheck.Util.Specialisation

import public Control.Monad.Either

import public Data.DPair
import public Data.List.Ex
import public Data.List.Map
import public Data.SortedMap
import public Data.SortedMap.Extra
import public Data.SortedSet

import public Deriving.DepTyCheck.Gen.ForOneType.Interface

import public Deriving.SpecialiseData
import public Language.Reflection.Unify

import public Data.Hashable
import public Data.Hashable.Base

%default total

||| All argument values applied in an expression
|||
||| Used for convenience when traversing given arguments and their types
record AllApps where
  constructor MkAllApps
  explicitArgs : List TTImp
  autoArgs : List TTImp
  namedArgs : SortedMap Name TTImp

||| Insert an `AnyApp` into `AllApps`
addApp' : AnyApp -> AllApps -> AllApps
addApp' (PosApp s) = {explicitArgs $= (s ::)}
addApp' (NamedApp nm s) = {namedArgs $= insert nm s}
addApp' (AutoApp s) = {autoArgs $= (s ::)}
addApp' (WithApp s) = {explicitArgs $= (s ::)}

||| Make an `AllApps` out of a list of `AnyApp`
|||
||| Used in conjunction with `unAppAny`
mkAllApps : List AnyApp -> AllApps
mkAllApps laa = foldl (flip addApp') (MkAllApps [] [] empty) $ reverse laa

||| Pop a value from `AllApps` by argument name
|||
||| The argument/value is returned from `AllApps`
getNamed : Maybe Name -> AllApps -> (Maybe TTImp, AllApps)
getNamed Nothing ap = (Nothing, ap)
getNamed (Just x) ap =
  case lookup x ap.namedArgs of
    Nothing => (Nothing, ap)
    Just t => (Just t, {namedArgs $= delete x} ap)

||| Pop an argument value from `AllApps`, returning Nothing if no value is given
|||
||| The argument/value is returned from `AllApps`
getGiven : Arg -> AllApps -> (Maybe TTImp, AllApps)
getGiven (MkArg _ ImplicitArg name _) ap = getNamed name ap
getGiven (MkArg _ ExplicitArg name _) (MkAllApps (x :: xs) autoArgs namedArgs) = (Just x, MkAllApps xs autoArgs namedArgs)
getGiven (MkArg _ ExplicitArg name _) ap = getNamed name ap
getGiven (MkArg _ AutoImplicit name _) (MkAllApps explicitArgs (x :: xs) namedArgs) = (Just x, MkAllApps explicitArgs xs namedArgs)
getGiven (MkArg _ AutoImplicit name _) ap = getNamed name ap
getGiven (MkArg _ (DefImplicit x) Nothing _) ap = (Just x, ap)
getGiven (MkArg _ (DefImplicit x) (Just n) _) ap =
  case lookup n ap.namedArgs of
    Nothing => (Just x, ap)
    Just t => (Just t , {namedArgs $= delete n} ap)

||| Extract given values of arguments from `AllApps`
getGivens : List Arg -> AllApps -> List (Maybe TTImp)
getGivens [] aa = []
getGivens (x :: xs) aa = do
  let (mr, aa) = getGiven x aa
  mr :: getGivens xs aa

allQImpl : Monad m => TTImp -> m TTImp -> m TTImp
allQImpl pi@(IPi _ _ _ _ _ _) r = r
allQImpl _ _ = pure `(?)

||| Replace every non-function sub-expression with a question mark
|||
||| (x -> (y -> z) -> q) becomes (? -> (? -> ?) -> ?)
allQuestions : TTImp -> TTImp
allQuestions t = runIdentity $ mapATTImp' allQImpl t

||| An abstract "argument" of a generator
|||
||| Consists of a type constructor's argument and a possible given value
record GenArg where
  constructor MkGenArg
  arg : Arg
  given : Maybe TTImp

LogPosition GenArg where
  logPosition (MkGenArg a Nothing) = "\{fromMaybe "" a.name}"
  logPosition (MkGenArg a $ Just t) = "(\{fromMaybe "" a.name} := \{show t})"

unGA : List GenArg -> (List Arg, List (Maybe TTImp))
unGA [] = ([], [])
unGA (x :: xs) = let (ys, zs) = unGA xs in (x.arg :: ys, x.given :: zs)

(.isGenerated) : GenArg -> Bool
(.isGenerated) = isNothing . given

(.isGiven) : GenArg -> Bool
(.isGiven) = isJust . given

||| Determine if the argument should be specialised or passed through
(.isSpecialising) : Elaboration m => GenArg -> m Bool
(.isSpecialising) (MkGenArg a Nothing) = pure False
(.isSpecialising) (MkGenArg a $ Just g) = do
  let True = snd (unPi a.type) == `(Type)
    | _ => pure False
  case g of
    IVar _ n => do
      nInfo <- getInfo n
      case nInfo of
        [] => pure False
        _ => pure True
    _ => pure True

||| Extracts given values of arguments from a type invocation expression
export
getGivens' : NamesInfoInTypes => TTImp -> Maybe (List GenArg)
getGivens' t = do
  let (IVar _ tyName, aTerms) = unAppAny t
    | _ => Nothing
  let Just tyInfo = lookupType tyName
    | _ => Nothing
  Just $ map (uncurry MkGenArg) $ zip tyInfo.args $ getGivens tyInfo.args (mkAllApps aTerms)

||| Assemble a list of arguments and their given values from `callGen` inputs
mkArgs :
  NamesInfoInTypes =>
  (sig : GenSignature) ->
  List (Fin sig.targetType.args.length, Arg) ->
  List (Fin sig.targetType.args.length, TTImp) ->
  List GenArg
mkArgs sig [] _ = []
mkArgs sig ((_, x) :: xs) [] = MkGenArg x Nothing :: mkArgs sig xs []
mkArgs sig ((i1, x) :: xs) g@((i2, y) :: ys) =
  if i1 == i2
    then MkGenArg x (Just y) :: mkArgs sig xs ys
    else MkGenArg x Nothing  :: mkArgs sig xs g

singleArg : Nat -> GenArg -> (TTImp, List GenArg)
singleArg n (MkGenArg a v) = do
  let n : Name = fromString "lam^\{show n}"
  (IVar EmptyFC n, [MkGenArg (MkArg a.count a.piInfo (Just n) $ allQuestions a.type) v])

processArg : MonadLog m => NamesInfoInTypes => GenSignature -> Nat -> GenArg -> m (TTImp, List GenArg)

processArgs' : MonadLog m => NamesInfoInTypes => GenSignature -> Nat -> List GenArg -> m (List AnyApp, List GenArg)
processArgs' sig k [] = pure ([], [])
processArgs' sig k (x :: xs) = do
  (aT, l) <- assert_total $ processArg sig k x
  (recAA, l') <- processArgs' sig (k + length l) xs
  pure (appArg x.arg aT :: recAA, l ++ l')

processArg sig argIdx ga with (ga.given)
  processArg sig argIdx ga | Nothing = do
    logPoint DetailedDebug "deptycheck.util.specialisation" [sig, ga] "No given value, passing through"
    pure $ singleArg argIdx ga
  processArg sig argIdx ga | Just x = do
    let (appLhs, appTerms) = unAppAny x
    let IVar _ tyName = appLhs
      | _ => do
        logPoint DetailedDebug "deptycheck.util.specialisation" [sig, ga] "Given value head is not a variable, passing through"
        pure $ singleArg argIdx ga
    case lookupType tyName of
      Just tyInfo => do
        let (_ :: _) = appTerms
          | [] => do
            logPoint DetailedDebug "deptycheck.util.specialisation" [sig, ga] "Given a type invocation w/o arguments, specialising"
            pure (x, [])
        let givens = map (uncurry MkGenArg) $ zip tyInfo.args $ getGivens tyInfo.args (mkAllApps appTerms)
        logPoint DetailedDebug "deptycheck.util.specialisation" [sig, ga]
          "Given a type invocation, traversing arguments: \{show $ map (fromMaybe "" . name . arg) givens}"
        map (mapFst $ reAppAny appLhs) $ processArgs' sig argIdx $ takeWhile (.isGiven) givens
      Nothing => do
        if (snd (unPi ga.arg.type) == `(Type))
          then do
            logPoint DetailedDebug "deptycheck.util.specialisation" [sig, ga] "Given a non-global type expr, passing through"
            -- pure (x, [])
            pure $ singleArg argIdx ga
          else do
            logPoint DetailedDebug "deptycheck.util.specialisation" [sig, ga] "Given a non-type expr, passing through"
            pure $ singleArg argIdx ga

processArgs :
  MonadLog m =>
  NamesInfoInTypes =>
  (sig : GenSignature) ->
  List GenArg ->
  m (TTImp, List Arg, List $ Maybe TTImp)
processArgs sig ga = map (bimap (reAppAny $ IVar EmptyFC sig.targetType.name) unGA) $ processArgs' sig 0 ga

export
formGivenVals : Vect l _ -> List TTImp -> Vect l TTImp
formGivenVals []        _         = []
formGivenVals (_ :: xs) []        = `(_) :: formGivenVals xs []
formGivenVals (x :: xs) (y :: ys) = y    :: formGivenVals xs ys

genGivens : List (TTImp, Fin x, Arg) -> (s : SortedSet (Fin x) ** Vect s.size TTImp)
genGivens l = do
  let (l1, l2, l3) = unzip3 l
  let s = SortedSet.fromList l2
  let gv = formGivenVals (Vect.fromList $ Prelude.toList s) l1
  (s ** gv)

specTaskToName : TTImp -> Name
specTaskToName t = do
  let (_, lamBody) = unLambda t
  let (callee, _) = unAppAny lamBody
  let vname =
    case callee of
         (IVar _ n) => show $ snd $ unNS n
         x => show x
  fromString "\{vname}^\{show $ hash t}"

-- Using the monadic trick makes the performance *much* better.
specTaskToName' : Monad m => TTImp -> m Name
specTaskToName' t = do
  let (_, lamBody) = unLambda t
  let (callee, _) = unAppAny lamBody
  let vname =
    case callee of
         (IVar _ n) => show $ snd $ unNS n
         x => show x
  hash <- pure $ show $ hash t
  pure $ fromString "\{vname}^\{hash}.\{vname}^\{hash}"

nameUnambigAndVis : Elaboration m => Name -> m Bool
nameUnambigAndVis n = do
  [(_, vis)] <- getVis n
    | _ => pure False
  pure $ vis /= Private

allConstructorsVisible : Elaboration m => TypeInfo -> m Bool
allConstructorsVisible ti = do
  all id <$> traverse nameUnambigAndVis (name <$> ti.cons)

mkDPairHelper : Nat -> (Name -> TTImp) -> TTImp -> TTImp
mkDPairHelper 0 _ t = t
mkDPairHelper (S n) helper t = do
  let nn = fromString $ "dph^\{show n}"
  `(MkDPair ~(helper nn) ~(mkDPairHelper n helper t))

dPairHelper : Nat -> TTImp
dPairHelper 0 = `(?)
dPairHelper (S n) = `(DPair ? ~(dPairHelper n))

inSameNS : Name -> Name -> Name
inSameNS (NS ns _) n = NS ns n
inSameNS _ n = n

export %tcinline
specialiseIfNeeded :
  Elaboration m =>
  NamesInfoInTypes =>
  DerivationClosure m =>
  (sig : GenSignature) ->
  (fuel : TTImp) ->
  Vect sig.givenParams.size TTImp ->
  m $ Maybe (List Decl, TypeInfo, TTImp)
specialiseIfNeeded sig fuel givenParamValues = do
  logPoint DetailedDebug "deptycheck.util.specialisation" [sig] "Checking specialisation need for \{show givenParamValues}..."
  -- Check if there are any given type args, if not return Nothing
  let True = any (\a => snd (unPi a.type) == `(Type)) $ index' sig.targetType.args <$> Prelude.toList sig.givenParams
    | False => pure Nothing
  -- Check if all of the generated type's constructors are visible, if not return Nothing
  True <- allConstructorsVisible sig.targetType
    | False => pure Nothing
  -- Assemble the `GenArg`s from `GenSignature` and given values
  let givenIdxVals = Prelude.toList sig.givenParams `zipV` givenParamValues
  let genArgs = mkArgs sig (withIndex sig.targetType.args) givenIdxVals
  -- Check if at least one `GenArg` can be specialised upon (i.e. is a type argument and has a non-passthrough given value)
  specable <- traverse (.isSpecialising) genArgs
  let True = any id specable
    | False => pure Nothing
  -- Generate specialisation rhs, arguments, and given values
  (lambdaRet, fvArgs, givenSubst) <- processArgs sig genArgs
  let preNorm = foldr lam lambdaRet fvArgs
  logPoint DetailedDebug "deptycheck.util.specialisation" [sig] "Task before normalisation: \{show preNorm}"
  -- Normalise the specialisation lambda
  (lambdaTy, lambdaBody) <- normaliseTask fvArgs lambdaRet
  logPoint DetailedDebug "deptycheck.util.specialisation" [sig] "NormaliseTask returned: lambdaTy = \{show lambdaTy};"
  logPoint DetailedDebug "deptycheck.util.specialisation" [sig] "                        lambdaBody = \{show lambdaBody};"
  -- Generate specialised type name
  specName <- specTaskToName' lambdaBody
  logPoint DetailedDebug "deptycheck.util.specialisation" [sig] "Specialised type name: \{show specName}"
  -- Check if `NamesInfoInTypes` contains specialised type
  (specTy, specDecls) : (TypeInfo, List Decl) <- case lookupType specName of
    -- If not, try looking it up via elaborator
    Nothing => do
      info <- try (Just <$> getInfo' specName) (pure Nothing)
      case info of
        Nothing => do
        -- If not found at all, derive specialised type
          logPoint DetailedDebug "deptycheck.util.specialisation" [sig] "Specialised type not found, deriving..."
          Right (specTy, specDecls) <- runEitherT {m} {e=SpecialisationError} $ specialiseDataRaw specName lambdaTy lambdaBody
            | Left err => fail "INTERNAL ERROR: Specialisation \{show lambdaBody} failed with error \{show err}."
          logPoint DetailedDebug "deptycheck.util.specialisation" [sig] "Derived \{show specTy.name}"
          -- Declare derived type
          declare specDecls
          logPoint Trace "deptycheck.util.specialisation" [sig] "Declared specialised type \{show specTy.name}: \{show lambdaRet}"
          pure (specTy, [])
        Just specTy => do
          logPoint DetailedDebug "deptycheck.util.specialisation" [sig] "Found \{show specTy.name}"
          pure (specTy, [])
    Just specTy => do
      logPoint DetailedDebug "deptycheck.util.specialisation" [sig] "Found \{show specTy.name}"
      pure (specTy, [])
  -- Assert that all of the specialised type's arguments are named for the specialised generator's `GenSignature` (this property should always be true)
  let Yes stNamed = areAllTyArgsNamed specTy
    | No _ => fail "INTERNAL ERROR: Specialised type \{show specTy.name} does not have fully named arguments and constructors."
  -- Form new givens set and given value list
  let (newGP ** newGVals) = genGivens $ mapMaybe (\(a,b) => map (,b) a) $ zip givenSubst $ withIndex specTy.args
  -- Obtain the specialised generator call
  (inv, cg_rhs) <- callGen (MkGenSignature specTy newGP) fuel newGVals
  let inv : TTImp = case cg_rhs of
        Nothing => inv
        Just (n ** perm) => reorderGend False perm inv
  -- Use derived cast to convert result back to polymorphic type
  let generateds = sig.targetType.args.length `minus` sig.givenParams.size
  let inv : TTImp =
    if generateds == 0
        then `(map (cast @{~(var $ inSameNS specTy.name "mToP")}) $ ~inv)
        else
          `(the (Gen MaybeEmpty ~(dPairHelper generateds)) $ map (\invv =>
            case invv of
              ~(mkDPairHelper generateds bindVar (bindVar "inv")) => ~(mkDPairHelper generateds var `(cast @{~(var $ inSameNS specTy.name "mToP")} inv))) ~inv)
  pure $ Just (specDecls, specTy, inv)

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
import public Deriving.SpecialiseData.TaskFormation

import public Language.Reflection.Unify

import public Data.Hashable
import public Data.Hashable.Base

%default total

||| Determine if the argument should be specialised or passed through
(.isPassthrough) : Elaboration m => GenArg -> m Bool
(.isPassthrough) (MkGenArg a Nothing) = pure True
(.isPassthrough) (MkGenArg a $ Just g) = do
  let True = snd (unPi a.type) == `(Type)
    | _ => pure True
  case g of
    IVar _ n => do
      nInfo <- getInfo n
      case nInfo of
        [] => pure True
        _ => pure False
    _ => pure False

||| Assemble a list of arguments and their given values from `callGen` inputs
|||
||| The indices inside both given lists must be in ascending order
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

||| Given a set of given argument indices, convert a list of their values into a vector that can be fed to `callGen`
|||
||| The values should be listed for indices in ascending order
||| (i.e. how these indices would be sorted if we called `toList` on the set)
export
formGivenVals : (s : SortedSet _) -> List TTImp -> Vect s.size TTImp
formGivenVals a b = fgvImpl (Vect.fromList $ Prelude.toList a) b
  where
    fgvImpl : Vect l _ -> List TTImp -> Vect l TTImp
    fgvImpl []        _         = []
    fgvImpl (_ :: xs) []        = `(_) :: fgvImpl xs []
    fgvImpl (x :: xs) (y :: ys) = y    :: fgvImpl xs ys

genGivens : List (TTImp, Fin x, Arg) -> (s : SortedSet (Fin x) ** Vect s.size TTImp)
genGivens l = do
  let (l1, l2, l3) = unzip3 l
  let s = SortedSet.fromList l2
  let gv = formGivenVals s l1
  (s ** gv)

-- Using the monadic trick makes the performance *much* better.
specTaskToName : Monad m => TTImp -> m Name
specTaskToName t = do
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
  try (do
    _ : Unit <- check `(let x = ~(var n) in ())
    pure True) (pure False)

allConstructorsVisible : Elaboration m => TypeInfo -> m Bool
allConstructorsVisible ti = do
  all id <$> traverse (nameUnambigAndVis . name) ti.cons

mkDPairOfUnknowns : Nat -> (Name -> TTImp) -> TTImp -> TTImp
mkDPairOfUnknowns 0 _ t = t
mkDPairOfUnknowns (S n) helper t = do
  let nn = fromString $ "dph^\{show n}"
  `(MkDPair ~(helper nn) ~(mkDPairOfUnknowns n helper t))

dPairOfUnknowns : Nat -> TTImp
dPairOfUnknowns 0 = `(?)
dPairOfUnknowns (S n) = `(DPair ? $ \_ => ~(dPairOfUnknowns n))

inSameNS : (nsSource: Name) -> Name -> Name
inSameNS (NS ns _) n = NS ns n
inSameNS _ n = n

export
specialiseIfNeeded :
  Elaboration m =>
  NamesInfoInTypes =>
  ConsRecs =>
  DerivationClosure m =>
  (sig : GenSignature) ->
  (fuel : TTImp) ->
  Vect sig.givenParams.size TTImp ->
  m $ Maybe TTImp
specialiseIfNeeded sig fuel givenParamValues = do
  logPoint DetailedDebug "deptycheck.derive.specialisation" [sig] "Checking specialisation need for \{show givenParamValues}..."
  -- Check if there are any given type args, if not return Nothing
  let True = any (\a => snd (unPi a.type) == `(Type)) $ index' sig.targetType.args <$> Prelude.toList sig.givenParams
    | False =>
      logValue DetailedDebug "deptycheck.derive.specialisation" [sig]
        "Not found any given type args, specialisation not needed."
        Nothing
  -- Check if all of the generated type's constructors are visible, if not return Nothing
  True <- allConstructorsVisible sig.targetType
    | False =>
      logValue DetailedDebug "deptycheck.derive.specialisation" [sig]
        "\{sig.targetType.name} has invisible constructors, specialisation impossible."
        Nothing
  -- Assemble the `GenArg`s from `GenSignature` and given values
  let givenIdxVals = Prelude.toList sig.givenParams `zipV` givenParamValues
  let genArgs = mkArgs sig (withIndex sig.targetType.args) givenIdxVals
  -- Check if at least one `GenArg` can be specialised upon (i.e. is a type argument and has a non-passthrough given value)
  -- We need to terminate when all givens are passthrough, because otherwise we'll be stuck endlessly performing
  -- identity specialisations of the same type
  False <- all id <$> traverse (.isPassthrough) genArgs
    | True =>
      logValue DetailedDebug "deptycheck.derive.specialisation" [sig]
        "Not found any type arguments that can be specialised upon, specialisation impossible."
        Nothing
  -- Generate specialisation rhs, arguments, and given values
  (lambdaRet, fvArgs, givenSubst) <- argsToSpecTask specDecideArg sig.targetType.name genArgs
  let preNorm = foldr lam lambdaRet fvArgs
  logPoint DetailedDebug "deptycheck.derive.specialisation" [sig] "Task before normalisation: \{show preNorm}"
  -- Normalise the specialisation lambda
  (lambdaTy, lambdaBody) <- normaliseTask fvArgs lambdaRet
  logPoint DetailedDebug "deptycheck.derive.specialisation" [sig] "NormaliseTask returned: lambdaTy = \{show lambdaTy};"
  logPoint DetailedDebug "deptycheck.derive.specialisation" [sig] "                        lambdaBody = \{show lambdaBody};"
  -- Generate specialised type name
  specName <- specTaskToName lambdaBody
  logPoint DetailedDebug "deptycheck.derive.specialisation" [sig] "Specialised type name: \{show specName}"
  -- Check if `NamesInfoInTypes` contains specialised type
  (specTy, specDecls) : (TypeInfo, List Decl) <- case lookupType specName of
    -- If not, try looking it up via elaborator
    Nothing => do
      info <- try (Just <$> getInfo' specName) (pure Nothing)
      case info of
        Nothing => do
        -- If not found at all, derive specialised type
          logPoint DetailedDebug "deptycheck.derive.specialisation" [sig] "Specialised type not found, deriving..."
          thisNS <- do
            NS nsn _ <- inCurrentNS ""
            | _ => fail "Internal error: inCurrentNS did not return NS"
            pure nsn
          Right (specTy, specDecls) <- runEitherT {m} {e=SpecialisationError} $
              specialiseDataRaw {nsProvider = inNS thisNS} specName lambdaTy lambdaBody
            | Left err => fail "INTERNAL ERROR: Specialisation \{show lambdaBody} failed with error \{show err}."
          logPoint DetailedDebug "deptycheck.derive.specialisation" [sig] "Derived \{show specTy.name}"
          -- Declare derived type
          declare specDecls
          specTy <- getInfo' specName
          logValue Trace "deptycheck.derive.specialisation" [sig]
            "Declared specialised type \{show specTy.name}: \{show lambdaRet}"
            (specTy, [])
        Just specTy =>
          logValue DetailedDebug "deptycheck.derive.specialisation" [sig]
            "Found \{show specTy.name}"
            (specTy, [])
    Just specTy =>
      logValue DetailedDebug "deptycheck.derive.specialisation" [sig]
        "Found \{show specTy.name}"
        (specTy, [])
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
          `(the (Gen MaybeEmpty ~(dPairOfUnknowns generateds)) $ map (\invv =>
            case invv of
              ~(mkDPairOfUnknowns generateds bindVar (bindVar "inv")) =>
                  ~(mkDPairOfUnknowns generateds var `(cast @{~(var $ inSameNS specTy.name "mToP")} inv))) ~inv)
  pure $ Just inv

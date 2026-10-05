module Deriving.SpecialiseData.TaskFormation

import public Language.Reflection
import public Language.Reflection.Syntax
import public Language.Reflection.Compat.TypeInfo
import public Language.Reflection.Logging

allQImpl : Monad m => NamesInfoInTypes => TTImp -> TTImp -> m TTImp
allQImpl (IPi {}) r = pure r
allQImpl (IApp {}) (IApp _ (Implicit {}) _) = pure `(?)
allQImpl (IApp {}) r@(IApp {}) = pure r
allQImpl (IApp {}) _ = pure `(?)
allQImpl v@(IVar _ n) _ =
  case lookupType n of
    Just _ => pure v
    Nothing => pure `(?)
allQImpl _ _ = pure `(?)

||| Replace every non-function sub-expression with a question mark
|||
||| (x -> (y -> z) -> q) becomes (? -> (? -> ?) -> ?)
allQuestions : NamesInfoInTypes => TTImp -> TTImp
allQuestions t = runIdentity $ mapMTTImp' allQImpl t

||| Information about a generator's argument extracted from GenSignature
|||
||| Consists of a type constructor's argument (`arg`) and a `Maybe` describing its potential given value (`given`)
public export
record GenArg where
  constructor MkGenArg
  arg : Arg
  given : Maybe TTImp

export
LogPosition GenArg where
  logPosition (MkGenArg a Nothing) = "\{fromMaybe "<unnamed arg>" a.name}"
  logPosition (MkGenArg a $ Just t) = "(\{fromMaybe "<unnamed arg>" a.name} := \{show t})"

unGA : List GenArg -> (List Arg, List (Maybe TTImp))
unGA [] = ([], [])
unGA (x :: xs) = let (ys, zs) = unGA xs in (x.arg :: ys, x.given :: zs)

(.isGenerated) : GenArg -> Bool
(.isGenerated) = isNothing . given

(.isGiven) : GenArg -> Bool
(.isGiven) = isJust . given

singleArg : NamesInfoInTypes => Nat -> GenArg -> (TTImp, List GenArg)
singleArg n (MkGenArg a v) = do
  let n : Name = fromString "lam^\{show n}"
  (IVar EmptyFC n, [MkGenArg (MkArg a.count a.piInfo (Just n) $ allQuestions a.type) v])

public export
data ArgDecision = Passthrough | SpecLit TTImp | SpecRec Name (List GenArg)

isPassthrough : ArgDecision -> Bool
isPassthrough Passthrough = True
isPassthrough _ = False

export
specDecideArg : NamesInfoInTypes => GenArg -> (ArgDecision, String)
specDecideArg ga with (ga.given)
  specDecideArg ga | Nothing = (Passthrough, "No given value")
  specDecideArg ga | Just x = do
    let (appLhs, appTerms) = unAppAny x
    let IVar _ tyName = appLhs
      | IPrimVal _ (PrT _) => (SpecLit x, "Given a primitive type invocation")
      | _ => (Passthrough, "Given value head is not a variable")
    case lookupType tyName of
      Just tyInfo => case appTerms of
        [] => (SpecLit x, "Given a type invocation w/o arguments")
        _ => do
          let givens = map (uncurry MkGenArg) $ zip tyInfo.args $ popArgVals tyInfo.args (mkAllApps appTerms)
          (SpecRec tyName givens, "Given a type invocation")
      Nothing =>
        ( Passthrough
        , if (snd (unPi ga.arg.type) == `(Type))
            then "Given a non-global type expr"
            else "Given a non-type expr")

processArg :
  MonadLog m =>
  NamesInfoInTypes =>
  (GenArg -> (ArgDecision, String)) ->
  Name ->
  Nat ->
  GenArg ->
  m (TTImp, List GenArg)

processArgs :
  MonadLog m =>
  NamesInfoInTypes =>
  (GenArg -> (ArgDecision, String)) ->
  Name ->
  Nat ->
  List GenArg ->
  m (List AnyApp, List GenArg)
processArgs dec tyName k [] = pure ([], [])
processArgs dec tyName k (x :: xs) = do
  (aT, l) <- assert_total $ processArg dec tyName k x
  (recAA, l') <- processArgs dec tyName (k + length l) xs
  pure (appArg x.arg aT :: recAA, l ++ l')

processArg dec tyName argIdx ga =
  case dec ga of
    (Passthrough, s) =>
      logValue DetailedDebug "specialiseData.taskFormation" [tyName, ga]
        "\{s}, passing through" $ singleArg argIdx ga
    (SpecLit x, s) =>
      logValue DetailedDebug "specialiseData.taskFormation" [tyName, ga]
        "\{s}, specialising" (x, [])
    (SpecRec n givens, s) => do
      logPoint DetailedDebug "specialiseData.taskFormation" [tyName, ga]
        "\{s}, traversing arguments: \{show $ map (fromMaybe "" . name . arg) givens}"
      map (mapFst $ reAppAny (IVar EmptyFC n)) $ processArgs dec n argIdx $ takeWhile (.isGiven) givens

export
argsToSpecTask :
  MonadLog m =>
  NamesInfoInTypes =>
  (GenArg -> (ArgDecision, String)) ->
  Name ->
  List GenArg ->
  m (TTImp, List Arg, List $ Maybe TTImp)
argsToSpecTask dec tyName ga = bimap (reAppAny $ IVar EmptyFC tyName) unGA <$> processArgs dec tyName 0 ga

allAppsToGenArgs : List Arg -> AllApps -> List GenArg
allAppsToGenArgs [] aa = []
allAppsToGenArgs (x :: xs) aa = do
  let pav = popArgVal x aa
  let mr = fst <$> pav
  let aa = fromMaybe aa $ snd <$> pav
  MkGenArg x mr :: allAppsToGenArgs xs aa

export
exprToSpecTask :
  MonadLog m =>
  NamesInfoInTypes =>
  (GenArg -> (ArgDecision, String)) ->
  TTImp ->
  m $ Maybe (TTImp, List Arg, List $ Maybe TTImp)
exprToSpecTask dec expr = do
  let (appHead, appTerms) = unAppAny expr
  let (IVar _ tyName) = appHead
    | _ => logValue DetailedDebug "specialiseData.taskFormation" []
              "Head of expression is not a variable: \{show appHead}"
              Nothing
  let (Just tyInfo) = lookupType tyName
    | _ => logValue DetailedDebug "specialiseData.taskFormation" []
              "\{tyName} is not a global type"
              Nothing
  let allApps = mkAllApps appTerms
  let genArgs = allAppsToGenArgs tyInfo.args allApps
  let False = all isPassthrough $ fst . dec <$> genArgs
    | True => logValue DetailedDebug "specialiseData.taskFormation" []
                "No non-passthrough arguments!"
                Nothing
  Just <$> argsToSpecTask dec tyName genArgs

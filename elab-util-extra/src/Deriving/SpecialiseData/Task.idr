module Deriving.SpecialiseData.Task

import public Control.Monad.Error.Interface
import public Data.DPair
import Deriving.SpecialiseData.Common
import Deriving.SpecialiseData.Helpers
import Deriving.SpecialiseData.TypeInfoExt
import Language.Reflection.Compat
import public Language.Reflection.Compat.TypeInfo
import Language.Reflection.Expr
import Language.Reflection.VarSubst

--------------------------------
--- SPECIALISATION TASK TYPE ---
--------------------------------

||| Specialisation task
public export
record SpecTask where
  constructor MkSpecTask
  ||| Full unification task
  tqArgs              : List Arg
  tqRet               : TTImp
  {auto 0 tqArgsNamed : All IsNamedArg tqArgs}
  ||| Unification task type
  ttArgs              : List Arg
  {auto 0 ttArgsNamed : All IsNamedArg ttArgs}
  ||| Namespace in which specialiseData was called
  currentNs           : Namespace
  ||| Name of specialised type
  resultName          : Name
  ||| Invocation of polymorphic type extracted from unification task
  fullInvocation      : TTImp
  ||| Invocation of specialised type given default arguents
  specInvocation      : TTImp
  ||| Polymorphic type's TypeInfo
  polyTy              : TypeInfo
  ||| Proof that all the constructors of the polymorphic type are named
  {auto 0 polyTyNamed : AllTyArgsNamed polyTy}

export
Show SpecTask where
  showPrec p t =
    showCon p "SpecTask" $ joinBy "" $
      [ showArg t.tqArgs
      , showArg t.tqRet
      , showArg t.ttArgs
      , showArg t.currentNs
      , showArg t.resultName
      , showArg t.fullInvocation
      , showArg t.specInvocation
      , showArg "<polyTy>"
      ]


---------------------
--- TASK ANALYSIS ---
---------------------

||| Given a list of arguments and a sorted set of names,
||| assert that every argument's name is in that set
checkArgsUse : MonadError SpecialisationError m => List Arg -> SortedSet Name -> m ()
checkArgsUse [] _ = pure ()
checkArgsUse (x :: xs) t = do
  let Just n = x.name
  | _ => checkArgsUse xs t
  if contains n t
    then checkArgsUse xs t
    else throwError UnusedVarError

||| Given a list of arguments and a list of their aliases, apply aliases to then
applyArgAliases :
  (as : List Arg) ->
  (0 _ : All IsNamedArg as) =>
  List (Name, Name) ->
  SortedMap Name TTImp ->
  Subset (List Arg) (All IsNamedArg)
applyArgAliases []        @{[]}     _  _   = Element [] []
applyArgAliases (x :: xs) @{_ :: _} ys ins = do
  let (newIns, newName, ys) : (SortedMap _ _, Name, List (Name, Name)) =
    case ys of
       []              => (ins                  , argName x, [])
       ((y, y') :: ys) => (insert y (var y') ins, y'       , ys)
  let Element rec prec = applyArgAliases xs ys newIns
  Element
    (MkArg x.count x.piInfo (Just newName) (substituteVariables newIns x.type) :: rec)
    (ItIsNamed :: prec)

||| Given a list of arguments, generate a list of aliased arguments
||| and a list of aliases
transformArgNames :
  (f : Name -> Name) ->
  (as : List Arg) ->
  (0 _ : All IsNamedArg as) =>
  (Subset (List Arg) (All IsNamedArg), List (Name, Name))
transformArgNames f as = do
  let aliases = pushIn as %search <&> \(x `Element` xN) => (argName x, f $ Expr.argName x @{xN})
  (applyArgAliases as aliases empty, aliases)

inGenNSImpl : Namespace -> Name -> Name -> Name
inGenNSImpl (MkNS strs) p n = do
  let newNS =
    case n of
        (NS (MkNS subs) n) => subs
        n => []
  NS (MkNS $ newNS ++ show p :: strs) $ dropNS n

||| Prepend namespace into which everything is generated to name
export
inGenNS : SpecTask -> Name -> Name
inGenNS task = inGenNSImpl task.currentNs task.resultName


||| Get all the information needed for specialisation from task
export
getTask :
  Monad m =>
  NamespaceProvider m =>
  MonadError SpecialisationError m =>
  NamesInfoInTypes =>
  (resultName : Name) ->
  (resultKind : TTImp) ->
  (resultContent : TTImp) ->
  m SpecTask
getTask resultName resultKind resultContent = do
  let (tqArgs, tqRet) = unLambda resultContent
  -- Check for unused arguments
  checkArgsUse tqArgs $ usesVariables tqRet
  -- Extract name of polymorphic type
  let (IVar _ typeName, _) = Expr.unAppAny tqRet
  | _ => throwError TaskTypeExtractionError
  -- Prove that all spec lambda arguments are named
  let Yes tqArgsNamed = all isNamedArg tqArgs
  | _ => throwError UnnamedArgInLambdaError
  -- Create aliases for spec lambda's arguments and perform substitution
  let (Element tqArgs tqArgsNamed, tqAlias) = transformArgNames (prependS "fv^\{resultName}^") tqArgs
  let tqRet = substituteVariables (fromList $ mapSnd var <$> tqAlias) tqRet
  let (ttArgs, _) = unPi resultKind
  -- Check for partial application in spec
  let True = (length tqArgs == length ttArgs)
  | _ => throwError PartialSpecError
  -- Prove that all spec lambda type's arguments are named
  let Yes ttArgsNamed = all isNamedArg ttArgs
  | _ => throwError UnnamedArgInLambdaError
  -- Apply aliasing to spec lambda type's info
  let Element ttArgs ttArgsNamed = applyArgAliases ttArgs tqAlias empty
  -- Get current namespace
  currentNs <- provideNS
  -- Get polymorphic type's info
  let Just polyTy = lookupType typeName
  | _ => throwError $ MissingTypeInfoError typeName
  -- Prove all its arguments/constructors/constructor arguments are named
  let Yes polyTyNamed = areAllTyArgsNamed polyTy
    | No _ => throwError $ UnnamedArgInPolyTyError polyTy.name
  let specInvocation = reAppAny
          (var (inGenNSImpl currentNs (snd $ unNS $ resultName) (snd $ unNS $ resultName))) $
            ttArgs.appsWith @{ttArgsNamed} var empty
  pure $ MkSpecTask
    { tqArgs
    , tqRet
    , tqArgsNamed
    , ttArgs
    , ttArgsNamed
    , currentNs
    , resultName = snd $ unNS resultName
    , fullInvocation = tqRet --- TODO: intelligent full invocation
    , specInvocation
    , polyTy
    , polyTyNamed
    }


||| Generate IPi with implicit type arguments and given return
export
forallMTArgs : SpecTask -> TTImp -> TTImp
forallMTArgs t = flip (foldr pi) $ makeTypeArgM0 . hideExplicitArg <$> t.ttArgs

export
applyMTArgs : SpecTask -> TTImp -> TTImp
applyMTArgs t =
  flip (foldl (\x,arg => x .! (fromMaybe "" arg.name, var $ fromMaybe "" arg.name))) $
    makeTypeArgM0 . hideExplicitArg <$> t.ttArgs

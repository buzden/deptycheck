module Deriving.SpecialiseData.Codegen

import public Data.DPair
import Data.Fin
import Data.SnocList
import Data.SnocList.Quantifiers
import Deriving.SpecialiseData.Common
import Deriving.SpecialiseData.Helpers
import Deriving.SpecialiseData.QuantifiersExt
import Deriving.SpecialiseData.Task
import Deriving.SpecialiseData.TaskFormation
import Deriving.SpecialiseData.TypeInfoExt
import Deriving.SpecialiseData.Unification
import Language.Reflection.Compat
import Language.Reflection.Expr
import public Language.Reflection.Unify
import public Language.Reflection.VarSubst

-----------------------------------
--- SPECIALISED TYPE GENERATION ---
-----------------------------------

||| Generate argument of a specified constructor
mkSpecArg : (ur : UnificationResult) -> Fin (ur.uniDg.freeVars) -> Subset Arg IsNamedArg
mkSpecArg ur fvId = do
  let fvData = index fvId ur.uniDg.fvData
  let fromLambda = finToNat fvId >= ur.task.lfv
  let rig = if fromLambda then M0 else fvData.rig
  let piInfo = if fromLambda && (fvData.piInfo == ExplicitArg) then ImplicitArg else fvData.piInfo
  Element (MkArg rig piInfo (Just fvData.name) fvData.type) ItIsNamed

getVar : TTImp -> Maybe Name
getVar (IVar _ n) = Just n
getVar _ = Nothing

||| Internal state of recursion search algorithm
record RecursionSearchState where
  constructor MkRSS
  ||| Accumulated transformation to cast from argument type to specialised type
  mToPRenames : SortedMap Name TTImp
  ||| Accumulated transformation to cast from specialised type to argument type
  pToMRenames : SortedMap Name TTImp
  ||| SnocList containing recursiveness of previous arguments
  areArgsRecursive : SnocList Bool
  ||| The pre-baked arguments to run unification with.
  argsForUnifier : Subset (Vect (length areArgsRecursive) Arg) (All IsNamedArg)
  ||| Accumulated arguments to be used in specialised constructor
  argsOutput : Subset (SnocList Arg) (All IsNamedArg)

parameters (t : SpecTask)
  ||| Check if a given argument is "recursive" (i.e. its type can be replaced with invocation of specialised type)
  checkArgRecursion :
    Monad m =>
    CanUnify m =>
    MonadLog m =>
    NamesInfoInTypes =>
    RecursionSearchState -> Subset Arg IsNamedArg -> m RecursionSearchState
  checkArgRecursion rss (Element thisArg thisArgNamed) = do
    let (MkRSS cRenames pToMRenames areArgsRec (Element argsForUni _) (Element argsOut _)) = rss
    let (aLhs, aa) = unAppAny thisArg.type
    let True = (length aa /= 0) || (isJust $ lookupType =<< getVar aLhs)
      | False => do
        let outPiInfo = substituteVariables cRenames <$> thisArg.piInfo
        let outType = substituteVariables cRenames thisArg.type
        let Element outArg outArgNamed =
            Element (MkArg thisArg.count outPiInfo (Just $ argName thisArg) outType) ItIsNamed
        pure $
          MkRSS
            cRenames
            pToMRenames
            (areArgsRec :< False)
            (Element (snoc argsForUni thisArg) (snoc %search thisArgNamed))
            (Element (argsOut :< outArg) (%search :< outArgNamed))
    let Element ta _ = fromListAll t.tqArgs @{t.tqArgsNamed}
    let uniTask = MkUniTask {lfv=_} argsForUni thisArg.type {rfv=_} ta t.fullInvocation
    ur <- unify uniTask
    case ur of
      Success ur => do
        let typeArgs = t.ttArgs.appsWith @{t.ttArgsNamed} var ur.fullResult
        logPoint DetailedDebug "specialiseData.fra" [] $ show ur.fullResult
        let tyRet = reAppAny (var t.resultName) typeArgs
        logPoint DetailedDebug "specialiseData.fra" [] $ show tyRet
        let mToPImpl = var $ inGenNS t "mToPImpl"
        let pToMImpl = var $ inGenNS t "pToMImpl"
        let outPiInfo = (\x => `(cast ~x)) . substituteVariables cRenames <$> thisArg.piInfo
        let outType = substituteVariables cRenames tyRet
        let Element outArg outArgNamed =
            Element (MkArg thisArg.count outPiInfo (Just $ argName thisArg) outType) ItIsNamed
        pure $
          MkRSS
            (insert (argName thisArg) `(~mToPImpl ~(var $ argName thisArg)) cRenames)
            (insert (argName thisArg) `(~pToMImpl ~(var $ argName thisArg)) pToMRenames)
            (areArgsRec :< True)
            (Element (snoc argsForUni thisArg) (snoc %search thisArgNamed))
            (Element (argsOut :< outArg) (%search :< outArgNamed))
      _ => do
        let outPiInfo = substituteVariables cRenames <$> thisArg.piInfo
        let outType = substituteVariables cRenames thisArg.type
        let Element outArg outArgNamed =
            Element (MkArg thisArg.count outPiInfo (Just $ argName thisArg) outType) ItIsNamed
        pure $
          MkRSS
            cRenames
            pToMRenames
            (areArgsRec :< False)
            (Element (snoc argsForUni thisArg) (snoc %search thisArgNamed))
            (Element (argsOut :< outArg) (%search :< outArgNamed))

  ||| Generate a specialised constructor
  export
  mkSpecCon :
    Monad m =>
    CanUnify m =>
    MonadLog m =>
    NamesInfoInTypes =>
    (params : SpecialisationParams) =>
    (newArgs : List Arg) ->
    (0 _ : All IsNamedArg newArgs) =>
    UnificationResult ->
    (con : Con) ->
    (0 _ : ConArgsNamed con) =>
    Nat ->
    m $ (Subset Con ConArgsNamed, ConMeta)
  mkSpecCon newArgs ur pCon cIdx = do
    let specArgs = mkSpecArg ur <$> ur.order
    let Element args allArgs =
      pullOut specArgs
    let typeArgs = newArgs.appsWith var ur.fullResult
    let tyRet = reAppAny (var t.resultName) typeArgs
    let n = if params.eraseConNames then fromString "\{t.resultName}^Con^\{show cIdx}" else dropNS pCon.name
    rssRhs <- foldlM checkArgRecursion (MkRSS empty empty [<] (Element [] []) (Element [<] [<])) specArgs
    let (MkRSS mToPRenames pToMRenames argsAreRecursive' _ (Element outArgs' outArgsNamed')) = rssRhs
    let Element outArgs outArgsNamed = toListAll outArgs' outArgsNamed'
    let conMeta = MkCMeta (MkAMeta <$> toList argsAreRecursive') mToPRenames pToMRenames
    pure $ (MkCon
      { name = inGenNS t $ n
      , args = outArgs
      , type = substituteVariables mToPRenames tyRet
      } `Element` TheyAreNamed outArgsNamed, conMeta)

  ||| Generate a specialised type
  export
  mkSpecTy :
    Monad m => CanUnify m => MonadLog m =>
    SpecialisationParams => NamesInfoInTypes =>
    UniResults -> m $ (Subset TypeInfo AllTyArgsNamed, TypeMeta)
  mkSpecTy ur = do
    let 0 _ = t.ttArgsNamed
    let muc = mapUCons t (mkSpecCon t.ttArgs) ur
    specConsMeta <- traverse id muc
    let (specCons, specMeta) = unzip specConsMeta
    let Element cons consAreNamed = pullOut specCons
    pure $ (MkTypeInfo
      { name = inGenNS t t.resultName
      , args = t.ttArgs
      , cons
      } `Element` TheyAllAreNamed t.ttArgsNamed consAreNamed, MkTyMeta specMeta)



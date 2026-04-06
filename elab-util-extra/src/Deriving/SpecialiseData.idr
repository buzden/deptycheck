module Deriving.SpecialiseData

import Control.Monad.Either
import Control.Monad.Trans
import Data.DPair
import Data.Either
import Data.Fin.Set
import Data.List
import public Data.List.Map -- workaround for compiler bug
import Data.List.Quantifiers
import Data.List1
import Data.Maybe
import Data.SnocList
import Data.SnocList.Quantifiers
import Data.SortedMap
import Data.SortedMap.Dependent
import Data.SortedSet
import Data.Vect
import Data.Vect.Quantifiers
import public Decidable.Decidable
import public Decidable.Equality
import Deriving.Show
import public Language.Mk
import Language.Reflection.Compat
import Language.Reflection.Compat.Constr
import public Language.Reflection.Compat.TypeInfo -- workaround for compiler bug
import Language.Reflection.Expr
import Language.Reflection.Syntax
import Language.Reflection.Logging
import public Language.Reflection.Unify.Interface
import public Language.Reflection.VarSubst -- workaround for compiler bug
import Syntax.IHateParens

%language ElabReflection

%default total

---------------------------------
--- SPECIALISATION ERROR TYPE ---
---------------------------------

||| Specialisation error
export
data SpecialisationError : Type where
  ||| Failed to extract polymorphic type name from task
  TaskTypeExtractionError   : SpecialisationError
  ||| Unused variable
  UnusedVarError            : SpecialisationError
  ||| Partial specification
  PartialSpecError          : SpecialisationError
  ||| Internal error
  InternalError             : String -> SpecialisationError
  ||| Lambda has unnamed arguments
  UnnamedArgInLambdaError   : SpecialisationError
  ||| Polymorphic type has unnamed arguments
  UnnamedArgInPolyTyError   : Name -> SpecialisationError
  ||| Failed to get TypeInfo
  |||
  ||| Can occur either due to trying to specialise a non-type invocation
  ||| or due to not having the necessary TypeInfo in the NamesInfoInTypes instance
  MissingTypeInfoError      : Name -> SpecialisationError

%hint
export
showSE : Show SpecialisationError
showSE = %runElab derive

-------------------------------
--- SPECIALISAION TASK TYPE ---
-------------------------------

||| Specialisation task
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

||| Unification results for the whole type
UniResults : Type
UniResults = List UnificationVerdict

------------------------
--- HELPER FUNCTIONS ---
------------------------

public export
record SpecialisationParams where
  constructor MkSpecParams
  eraseConNames : Bool

public export
%defaulthint
SpecialisationDefaults : SpecialisationParams
SpecialisationDefaults = MkSpecParams
  { eraseConNames = False
  }

public export
interface NamespaceProvider (0 m : Type -> Type) where
  constructor MkNSProvider
  provideNS : m Namespace

export
Monad m => MonadTrans t => NamespaceProvider m => NamespaceProvider (t m) where
  provideNS = lift provideNS

export
inNS : Monad m => Namespace -> NamespaceProvider m
inNS ns = MkNSProvider $ pure ns

export
%defaulthint
NoNS : Monad m => NamespaceProvider m
NoNS = inNS (MkNS [])

inGenNSImpl : Namespace -> Name -> Name -> Name
inGenNSImpl (MkNS strs) p n = do
  let newNS =
    case n of
        (NS (MkNS subs) n) => subs
        n => []
  NS (MkNS $ newNS ++ show p :: strs) $ dropNS n

||| Prepend namespace into which everything is generated to name
inGenNS : SpecTask -> Name -> Name
inGenNS task = inGenNSImpl task.currentNs task.resultName

||| Given a sequence of arguments, return list of argument name-BindVar pairs
argsToBindMap : Foldable f => f Arg -> List (Name, TTImp)
argsToBindMap = foldMap $ toList . map (\y => (y, bindVar y)) . name

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

prependS : String -> Name -> Name
prependS s n = UN $ Basic $ s ++ show n

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

||| Make an argument omega implicit if it is explicit
hideExplicitArg : Arg -> Arg
hideExplicitArg a = { piInfo := if a.piInfo == ExplicitArg then ImplicitArg else a.piInfo } a

||| Make an argument omega implicit
makeImplicit : Arg -> Arg
makeImplicit = { piInfo := ImplicitArg }

||| Make a type argument zero-count
makeTypeArgM0 : Arg -> Arg
makeTypeArgM0 a = { count := if a.type == `(Type) then M0 else a.count } a

||| A tuple value of multiple repeating expressions
tupleOfN : Nat -> TTImp -> TTImp
tupleOfN 0 _ = `(Unit)
tupleOfN 1 t = t
tupleOfN (S n) t = `(MkPair ~t ~(tupleOfN n t))

||| Assemble a TTImp of a tuple from a list of `TTImp`s
tupleOf : List TTImp -> TTImp
tupleOf [] = `(())
tupleOf [x] = x
tupleOf (x :: xs) = `(MkPair ~x ~(tupleOf xs))

||| Proof that hideExplicitArg doesn't affect namedness of arguments
hideExplicitArgPreservesNames :
  (args : List Arg) ->
  (0 _ : All IsNamedArg args) =>
  All IsNamedArg (SpecialiseData.hideExplicitArg <$> args)
hideExplicitArgPreservesNames [] @{[]} = []
hideExplicitArgPreservesNames (x :: xs) @{_ :: _} with (x)
  hideExplicitArgPreservesNames (x :: xs) @{_ :: _} | (MkArg _ _ (Just n) _) =
    ItIsNamed :: hideExplicitArgPreservesNames xs

||| Proof that makeImplicit doesn't affect namedness of arguments
makeImplicitPreservesNames :
  (args : List Arg) ->
  (0 _ : All IsNamedArg args) =>
  All IsNamedArg (SpecialiseData.makeImplicit <$> args)
makeImplicitPreservesNames [] @{[]} = []
makeImplicitPreservesNames (x :: xs) @{_ :: _} with (x) -- This `with` match is a workaround for coverage checking bug
  makeImplicitPreservesNames (x :: xs) @{_ :: _} | (MkArg _ _ (Just n) _) =
    ItIsNamed :: makeImplicitPreservesNames xs

||| Make all explicit arguments in list implicit
hideExplicitArgs : (xs : List Arg) -> (0 _ : All IsNamedArg xs) => Subset (List Arg) (All IsNamedArg)
hideExplicitArgs xs = hideExplicitArg <$> xs `Element` hideExplicitArgPreservesNames xs

||| Make all arguments in list implicit
makeArgsImplicit : (xs : List Arg) -> (0 _ : All IsNamedArg xs) => Subset (List Arg) (All IsNamedArg)
makeArgsImplicit xs = makeImplicit <$> xs `Element` makeImplicitPreservesNames xs

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

||| Remove named and auto-implicit applications of holes
cleanupHoleAutoImplicitsImpl : TTImp -> TTImp
cleanupHoleAutoImplicitsImpl (IAutoApp _ x (Implicit _ _)) = x
cleanupHoleAutoImplicitsImpl (INamedApp _ x _ (Implicit _ _)) = x
cleanupHoleAutoImplicitsImpl x = x

||| Generate an AnyApp for given Arg, with the argument value either
||| retrieved from the map if present or generated with `fallback`
(.appWith) :
  (arg : Arg) ->
  (0 _ : IsNamedArg arg) =>
  (fallback : Name -> TTImp) ->
  (argValues : SortedMap Name TTImp) ->
  AnyApp
(.appWith) arg@(MkArg _ _ (Just n) _) f argVals =
  appArg arg $ fromMaybe (f n) $ lookup n argVals

||| Generate a List AnyApp for given argument List,
||| with arguments retrieved from the map if present or generated with `fallback`
(.appsWith) :
  (args: List Arg) ->
  (0 _ : All IsNamedArg args) =>
  (fallback : Name -> TTImp) ->
  (argValues : SortedMap Name TTImp) ->
  List AnyApp
(.appsWith) [] _ _ = []
(.appsWith) (x :: xs) @{_ :: _} f argVals =
  x.appWith f argVals :: xs.appsWith f argVals


||| Get all the information needed for specialisation from task
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

namespace TypeInfoInvoke
  ||| Returns a full application of the given type constructor
  ||| with argument values sourced from `argValues`
  ||| or generated with `fallback` if not present
  export
  (.apply) :
    (ti : TypeInfo) ->
    (0 tiN : AllTyArgsNamed ti) =>
    (fallback : Name -> TTImp) ->
    (argValues : SortedMap Name TTImp) ->
    TTImp
  (.apply) t f vals = do
    reAppAny (var t.name) $ t.args.appsWith @{tiN.tyArgsNamed} f vals

namespace ConInvoke
  ||| Returns a full application of the given constructor
  ||| with argument values sourced from `argValues`
  ||| or generated with `fallback` if not present
  export
  (.apply) :
    (con : Con) ->
    (0 _ : ConArgsNamed con) =>
    (fallback : Name -> TTImp) ->
    (argValues : SortedMap Name TTImp) ->
    TTImp
  (.apply) con f vals = reAppAny (var con.name) $ con.args.appsWith f vals @{conArgsNamed}

namespace VectAll
  ||| Proof that Vect.All works over Vect.snoc
  export
  0 snoc: All p prev -> p new -> All p (Data.Vect.snoc prev new)
  snoc [] y = [y]
  snoc (y :: ys) z = y :: snoc ys z

  ||| List + List.All to Vect + Vect.All
  export
  fromListAll : (l : List t) -> (0 pr : All p l) => Subset (Vect (length l) t) (All p)
  fromListAll [] = Element [] []
  fromListAll (x :: xs) @{p :: ps} = do
    let Element xs' ps' = fromListAll xs @{ps}
    Element (x :: xs') (p :: ps')

namespace ListAll
  ||| Proof that List.All works over List.snoc
  export
  0 snoc : All p prev -> p new -> All p (Data.List.snoc prev new)
  snoc [] y = [y]
  snoc (y :: ys) z = y :: snoc ys z

namespace SnocListAll
  ||| SnocList + SnocList.All to List + List.All
  export
  toListAll : (sl : SnocList Arg) -> (0 _ : All p sl) -> Subset (List Arg) (All p)
  toListAll [<] [<] = Element [] []
  toListAll (sx :< x) (sy :< y) = do
    let Element xs ys = toListAll sx sy
    Element (snoc xs x) (snoc ys y)

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

||| Specialistaion-related constructor argument metadata
record ArgMeta where
  constructor MkAMeta
  ||| The argument's type can be substituted by specialised type invocation
  isRecursiveArg : Bool

||| Specialisation-related constructor metadat
record ConMeta where
  constructor MkCMeta
  ||| Metadata for each argument
  argMeta : List ArgMeta
  ||| Replacements to transform original argument's type to specialised type
  mToPRenames : SortedMap Name TTImp
  ||| Replacement to transform specialised type to original argument's type
  pToMRenames : SortedMap Name TTImp

hasRecursiveArgs : ConMeta -> Bool
hasRecursiveArgs = any isRecursiveArg . argMeta

countRecursiveArgs : ConMeta -> Nat
countRecursiveArgs = count isRecursiveArg  . argMeta

recursiveArgNames : Con -> ConMeta -> List Name
recursiveArgNames con meta = do
  let recursiveArgPairs = List.filter (isRecursiveArg . snd) $ zip con.args meta.argMeta
  fromMaybe "" . name . fst <$> recursiveArgPairs

||| Specialisation-related type metadata
record TypeMeta where
  constructor MkTyMeta
  ||| Specialisation-related metadata for each constructor
  conMeta : List ConMeta

||| Generate a constructor binding where only recursive arguments are bound.
||| Said arguments are also aliased via `alias` function.
bindConRecArgsAliased : Con -> ConMeta -> (Name -> Name) -> TTImp
bindConRecArgsAliased con meta alias =
  reAppAny (var con.name) $ processArg <$> zip con.args meta.argMeta
  where
  maybeBind : Arg -> ArgMeta -> TTImp
  maybeBind a am = if isRecursiveArg am then bindVar $ alias $ fromMaybe "" a.name else `(_)

  processArg : (Arg, ArgMeta) -> AnyApp
  processArg (a@(MkArg _ ExplicitArg _ _), am) = PosApp $ maybeBind a am
  processArg (a, am) = NamedApp (fromMaybe "" a.name) $ maybeBind a am

parameters (t : SpecTask)
  ---------------------------
  --- CONSTRUCTOR MAPPING ---
  ---------------------------
  ||| Run monadic operation on all constructors of specialised type
  mapCons :
    (f : (pCon : Con) ->
         (0 _ : ConArgsNamed pCon) =>
         r) ->
    List r
  mapCons f = do
    let adp = pushIn t.polyTy.cons t.polyTyNamed.tyConArgsNamed
    map (\(Element c pc) => f c) adp

  ||| Map over all constructors for which unification succeeded
  mapUCons :
    (f : UnificationResult ->
         (pCon : Con) ->
         (0 _ : ConArgsNamed pCon) =>
         Nat ->
         r) ->
    UniResults ->
    List r
  mapUCons f rs = do
    let adp = pushIn t.polyTy.cons t.polyTyNamed.tyConArgsNamed
    let f' : List (Subset Con ConArgsNamed) -> UniResults -> Nat -> List r
        f' (Element con _ :: xs) (Success res :: ys) n = f res con n :: f' xs ys (S n)
        f' (_ :: xs)             (_ :: ys)           n = f' xs ys n
        f' _ _ _ = []
    f' adp rs 0

  ||| Run monadic operation on all pairs of specified and polymorphic constructors
  map2UConsN :
    (f : UnificationResult ->
         (mt : TypeInfo) ->
         (0 _ : AllTyArgsNamed mt) =>
         (con : Con) ->
         (0 _ : ConArgsNamed con) =>
         (mcon : Con) ->
         (0 _ : ConArgsNamed mcon) =>
         ConMeta ->
         Nat ->
         r) ->
    UniResults ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    TypeMeta ->
    List r
  map2UConsN f rs mt @{mtp} meta = do
    let p1 = pushIn t.polyTy.cons t.polyTyNamed.tyConArgsNamed
    let p2 = pushIn mt.cons mtp.tyConArgsNamed
    f' 0 p1 p2 rs meta.conMeta
    where
      f' :
        Nat ->
        List (Subset Con ConArgsNamed) ->
        List (Subset Con ConArgsNamed) ->
        UniResults ->
        List ConMeta ->
        List r
      f' n (Element con _ :: xs) (Element mcon _ :: ys) (Success res :: zs) (meta' :: metas) =
        f res mt con mcon meta' n :: f' (S n) xs ys zs metas
      f' n (_             :: xs)                    ys  (_:: zs) ms =
        f' n xs ys zs ms
      f' _ _ _ _ _ = []

  -------------------------------
  --- CONSTRUCTOR UNIFICATION ---
  -------------------------------

  ||| Run unification for a given polymorphic constructor
  unifyCon : MonadLog m => (unifier : CanUnify m) => (con : Con) -> (0 conN : ConArgsNamed con) => m UnificationVerdict
  unifyCon con = logBounds Debug "specialiseData.unifyCon" [t.polyTy, con] $ do
    let Element ca _ = fromListAll con.args @{conArgsNamed}
    let Element ta _ = fromListAll t.tqArgs @{t.tqArgsNamed}
    let uniTask =
      MkUniTask {lfv=_} ca con.type
                {rfv=_} ta t.fullInvocation
    logPoint DetailedDebug "specialiseData.unifyCon" [t.polyTy, con] "Unifier task: \{show uniTask}"
    uniRes <- unify uniTask
    logPoint DetailedDebug "specialiseData.unifyCon" [t.polyTy, con] "Unifier output: \{show uniRes}"
    pure uniRes

  ---------------------------------
  --- SPECIFIED TYPE GENERATION ---
  ---------------------------------

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
  mkSpecTy :
    Monad m => CanUnify m => MonadLog m =>
    SpecialisationParams => NamesInfoInTypes =>
    UniResults -> m $ (Subset TypeInfo AllTyArgsNamed, TypeMeta)
  mkSpecTy ur = do
    let 0 _ = t.ttArgsNamed
    let muc = mapUCons (mkSpecCon t.ttArgs) ur
    specConsMeta <- traverse id muc
    let (specCons, specMeta) = unzip specConsMeta
    let Element cons consAreNamed = pullOut specCons
    pure $ (MkTypeInfo
      { name = inGenNS t t.resultName
      , args = t.ttArgs
      , cons
      } `Element` TheyAllAreNamed t.ttArgsNamed consAreNamed, MkTyMeta specMeta)

  mkSpecTySig : Decl
  mkSpecTySig = iDataLater Public t.resultName (piAll type t.ttArgs)

  ------------------------
  --- CLAIM DERIVATION ---
  ------------------------
  ||| Generate IPi with implicit type arguments and given return
  forallMTArgs : TTImp -> TTImp
  forallMTArgs = flip (foldr pi) $ makeTypeArgM0 . hideExplicitArg <$> t.ttArgs

  applyMTArgs : TTImp -> TTImp
  applyMTArgs =
    flip (foldl (\x,arg => x .! (fromMaybe "" arg.name, var $ fromMaybe "" arg.name))) $
      makeTypeArgM0 . hideExplicitArg <$> t.ttArgs

  ||| Generate specialised to polimorphic type conversion function signature
  mkMToPImplClaim : Decl
  mkMToPImplClaim = public' "mToPImpl" $ forallMTArgs $ arg t.specInvocation .-> t.fullInvocation

  ||| Generate specialised to polimorphic cast signature
  mkMToPClaim : Decl
  mkMToPClaim = interfaceHint Public "mToP" $ forallMTArgs $ `(Cast ~(t.specInvocation) ~(t.fullInvocation))

  ||| Decidable equality signatures
  mkDecEqImplClaim : Decl
  mkDecEqImplClaim =
    let tInv = t.specInvocation
    in public' "decEqImpl" $ forallMTArgs $
      piAll
        `(Dec (Equal {a = ~tInv} {b = ~tInv} x1 x2))
        [ MkArg MW AutoImplicit Nothing `(DecEq ~(t.fullInvocation))
        , MkArg MW ExplicitArg (Just "x1") tInv
        , MkArg MW ExplicitArg (Just "x2") tInv
        ]

  mkDecEqClaim : Decl
  mkDecEqClaim = interfaceHint Public "decEq'" $ forallMTArgs `(DecEq ~(t.fullInvocation) => DecEq ~(t.specInvocation))

  mkShowClaims : List Decl
  mkShowClaims =
    [ public' "showImpl" $
      forallMTArgs
        `(Show ~(t.fullInvocation) => ~(t.specInvocation) -> String)
    , public' "showPrecImpl" $
      forallMTArgs
        `(Show ~(t.fullInvocation) => Prec -> ~(t.specInvocation) -> String)
    , interfaceHint Public "show'" $ forallMTArgs $
      `(Show ~(t.fullInvocation) => Show ~(t.specInvocation))
    ]

  mkEqClaims : List Decl
  mkEqClaims = do
    let tInv = t.specInvocation
    [ public' "eqImpl" $ forallMTArgs
        `(Eq ~(t.fullInvocation) => ~tInv -> ~tInv -> Bool)
    , public' "neqImpl" $ forallMTArgs
        `(Eq ~(t.fullInvocation) => ~tInv -> ~tInv -> Bool)
    , interfaceHint Public "eq'" $ forallMTArgs $
        `(Eq ~(t.fullInvocation) => Eq ~tInv)
    ]

  ||| Generate specialised to polymorphic type conversion function signature
  mkPToMImplClaim : Decl
  mkPToMImplClaim = public' "pToMImpl" $ forallMTArgs $ arg t.fullInvocation .-> t.specInvocation

  ||| Generate specialised to polimorphic cast signature
  mkPToMClaim : Decl
  mkPToMClaim =
    interfaceHint Public "pToM" $ forallMTArgs $ `(Cast ~(t.fullInvocation) ~(t.specInvocation))

  mkFromStringClaims : List Decl
  mkFromStringClaims = do
    let tInv = t.specInvocation
    [ public' "fromStringImpl" $
        forallMTArgs
          `(FromString ~(t.fullInvocation) => String -> ~tInv)
    , interfaceHint Public "fromString'" $
        forallMTArgs `(FromString ~(t.fullInvocation) => FromString ~tInv)
    ]

  mkNumClaims : List Decl
  mkNumClaims = do
    let tInv = t.specInvocation
    [ public' "numImpl" $
        forallMTArgs
          `(Num ~(t.fullInvocation) => Integer -> ~tInv)
    , public' "plusImpl" $
        forallMTArgs
          `(Num ~(t.fullInvocation) => ~tInv -> ~tInv -> ~tInv)
    , public' "starImpl" $
        forallMTArgs
          `(Num ~(t.fullInvocation) => ~tInv -> ~tInv -> ~tInv)
    , interfaceHint Public "num'" $
        forallMTArgs `(Num ~(t.fullInvocation) => Num ~tInv)
    ]

  standardClaims : List Decl
  standardClaims =
    [ mkMToPImplClaim
    , mkMToPClaim
    , mkDecEqImplClaim
    , mkDecEqClaim
    ] ++ join
      [ mkShowClaims
      , mkEqClaims
      ]

  decidedClaims : List Decl
  decidedClaims =
    [ mkPToMImplClaim
    , mkPToMClaim
    ] ++ join
      [ mkFromStringClaims
      , mkNumClaims
      ]

  ------------------------------------
  --- POLY TO POLY CAST DERIVATION ---
  ------------------------------------

  transMachineVars : TTImp -> TTImp
  transMachineVars $ IVar fc n@(MN ns nn) = IVar fc $ fromString "MS^\{show ns}^\{show nn}"
  transMachineVars $ IBindVar fc n@(MN ns nn) = IBindVar fc $ fromString "MS^\{show ns}^\{show nn}"
  transMachineVars t = t


  ||| Generate specialised to polymorphic type conversion function clause
  ||| for given constructor
  mkMToPImplClause :
    UnificationResult ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    (pCon : Con) ->
    (0 _ : ConArgsNamed pCon) =>
    (mCon : Con) ->
    (0 _ : ConArgsNamed mCon) =>
    ConMeta ->
    Nat ->
    Clause
  mkMToPImplClause ur _ con mcon meta _ =
    mapClause transMachineVars $
      var "mToPImpl" .$
        mcon.apply bindVar
          (substituteVariables
            (fromList $ argsToBindMap mcon.args) <$> ur.fullResult)
      .= (substituteVariables meta.mToPRenames $ con.apply var ur.fullResult)

  ||| Generate specialised to polymorphic type conversion function declarations
  mkMToPImplDecls :
    UniResults ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    TypeMeta ->
    List Decl
  mkMToPImplDecls urs mt meta = do
    let clauses = map2UConsN mkMToPImplClause urs mt meta
    [ def "mToPImpl" clauses
    ]

  ||| Generate specialised to polymorphic cast signature
  mkMToPSig : (mt : TypeInfo) -> (0 _ : AllTyArgsNamed mt) => TTImp
  mkMToPSig mt = do
    forallMTArgs $ `(Cast ~(t.specInvocation) ~(t.fullInvocation))

  ||| Generate specialised to polymorphic cast declarations
  mkMToPDecls : (mt : TypeInfo) -> (0 _ : AllTyArgsNamed mt) => List Decl
  mkMToPDecls mt =
    [ def "mToP" [ (var "mToP") .= `(MkCast mToPImpl)]
    ]

  -----------------------------------
  --- CAST INJECTIVITY DERIVATION ---
  -----------------------------------

  ||| Emit a recursive call to castInjImpl constructing the proof from given names
  recCastInj : Name -> Name -> TTImp
  recCastInj p1 p2 = `(~(var $ inGenNS t $ "castInjImpl") $ trans ~(var p1) $ sym ~(var p2))

  ||| Generate a with-clause corresponding to a single recursive argument
  mkArgWithClause : Name -> TTImp -> Clause -> Clause
  mkArgWithClause argName existingLhs inner = do
    let mToPImpl = var $ inGenNS t "mToPImpl"
    let lhsArg = var $ fromString "lhs^\{argName}"
    let rhsArg = var $ fromString "rhs^\{argName}"
    let p1 = Just (MW, fromString "\{argName}^p1")
    let p2 = Just (MW, fromString "\{argName}^p2")
    withClause existingLhs MW `(~mToPImpl ~lhsArg) p1 [] [
      withClause `(~existingLhs | _) MW `(~mToPImpl ~rhsArg) p2 [] [inner]
    ]

  ||| Wrap a term into a number of `IAppWith`s with underscores
  withManyUnders : Nat -> TTImp -> TTImp
  withManyUnders 0 x = x
  withManyUnders (S n) x = withManyUnders n `(~x | _)

  ||| Generate a final with-clause that matches all equality proofs to `Refl`s
  mkFinalClause : (con : Con) -> (0 _ : ConArgsNamed con) => ConMeta -> Clause
  mkFinalClause con meta = do
    let emptyCon = con.apply (\_ => `(_)) empty
    let recArgAmount = countRecursiveArgs meta
    let initialLhs = withManyUnders (2 * recArgAmount) $
      var "castInjImpl" .! ("castInj^x", emptyCon) .! ("castInj^y", emptyCon) .$ var "Refl"
    let recNames = recursiveArgNames con meta
    let recFns = (\n => recCastInj (fromString "\{n}^p1") (fromString "\{n}^p2")) <$> recNames
    withClause initialLhs MW (tupleOf recFns) Nothing [] [
      `(~initialLhs | ~(tupleOfN recArgAmount `(Refl))) .= `(Refl)
    ]

  ||| Generate a left-hand-side for recursive argument with-clauses
  mkInitialLhs : Con -> ConMeta -> TTImp
  mkInitialLhs con meta = do
    let lhsCon = bindConRecArgsAliased con meta $ prependS "lhs^"
    let rhsCon = bindConRecArgsAliased con meta $ prependS "rhs^"
    var "castInjImpl" .! ("castInj^x", lhsCon) .! ("castInj^y", rhsCon) .$ bindVar "prf"

  ||| Wrap a clause in with-clauses for all given names
  mkRecArgClauses : List Name -> TTImp -> Clause -> Clause
  mkRecArgClauses [] exLhs inner = inner
  mkRecArgClauses (x :: xs) exLhs inner = mkArgWithClause x exLhs $ mkRecArgClauses xs `(~exLhs | _ | _) inner

  ||| Derive a single cast injectivity clause
  mkCastInjClause :
    UnificationResult ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    (con : Con) ->
    (0 cn : ConArgsNamed con) =>
    (mcon : Con) ->
    (0 mcn : ConArgsNamed mcon) =>
    ConMeta ->
    Nat ->
    Clause
  mkCastInjClause ur mt _ con meta n = do
    if not (hasRecursiveArgs meta)
      then do
        let emptyCon = con.apply (\_ => `(_)) empty
        (var "castInjImpl") .! ("castInj^x", emptyCon) .! ("castInj^y", emptyCon) .$ `(Refl) .= `(Refl)
      else do
        let finalClause = mkFinalClause con meta
        let recNames = recursiveArgNames con meta
        let initLhs = mkInitialLhs con meta
        mkRecArgClauses recNames initLhs finalClause

  ||| Derive cast injectivity proof
  mkCastInjDecls :
    UniResults ->
    (mt : TypeInfo) ->
    (0 mtp : AllTyArgsNamed mt) =>
    TypeMeta ->
    List Decl
  mkCastInjDecls ur ti meta = do
    let xVar = "castInj^x"
    let yVar = "castInj^y"
    let mToPVar = var $ inGenNS t "mToP"
    let mToPImplVar = applyMTArgs $ var $ inGenNS t "mToPImpl"
    let arg1 = MkArg MW ImplicitArg (Just xVar) $
                ti.apply var empty
    let arg2 = MkArg MW ImplicitArg (Just yVar) $
                ti.apply var empty
    let eqs =
      `((~(mToPImplVar .$ var xVar)
          ~=~
          ~(mToPImplVar .$ var yVar)) ->
          ~(var xVar) ~=~ ~(var yVar))
    let castInjImplClauses = map2UConsN mkCastInjClause ur ti meta
    [ claim M0 Public [] "castInjImpl" $ forallMTArgs $ pi arg1 $ pi arg2 $ eqs
    , def "castInjImpl" castInjImplClauses
    , claim M0 Public [Hint False] "castInj" $ forallMTArgs $
        `(Injective ~(mToPImplVar))
    , def "castInj" $ singleton $
        `(castInj) .= `(MkInjective castInjImpl)
    ]

  -------------------------------------
  --- DECIDABLE EQUALITY DERIVATION ---
  -------------------------------------

  ||| Decidable equality clause
  mkDecEqImplClause : Clause
  mkDecEqImplClause =
    let mToPImpl = var $ inGenNS t "mToPImpl"
    in `(decEqImpl x1 x2)
        .=
        `(decEqInj {f = ~mToPImpl} $
          let x1' : ~(t.fullInvocation);
              x1' = (~mToPImpl x1);
              x2' : ~(t.fullInvocation);
              x2' = (~mToPImpl x2);
          in decEq x1' x2')

  ||| Derive decidable equality
  mkDecEqDecls :
    UniResults ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    List Decl
  mkDecEqDecls _ ti = do
    [ def "decEqImpl" [ mkDecEqImplClause ]
    , def "decEq'"
      [ `(decEq') .= `((Mk DecEq) ~(var $ inGenNS t "decEqImpl")) ]
    ]

  -----------------------
  --- SHOW DERIVATION ---
  -----------------------

  ||| Derive Show implementation via cast
  mkShowDecls :
    UniResults ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    List Decl
  mkShowDecls _ ti = do
    let mToPImpl = var $ inGenNS t "mToPImpl"
    [ def "showImpl" [ `(showImpl x) .= `(show $ ~mToPImpl x) ]
    , def "showPrecImpl"
      [ `(showPrecImpl p x) .= `(showPrec p $ ~mToPImpl x) ]
    , def "show'" [ `(show') .= `(MkShow showImpl showPrecImpl) ]
    ]

  ---------------------
  --- EQ DERIVATION ---
  ---------------------

  ||| Derive Eq implementation via cast
  mkEqDecls :
    UniResults ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    List Decl
  mkEqDecls _ ti = do
    let mToPImpl = var $ inGenNS t "mToPImpl"
    [ def "eqImpl" [ `(eqImpl x y) .= `((~mToPImpl x) == (~mToPImpl y)) ]
    , def "neqImpl" [ `(neqImpl x y) .= `((~mToPImpl x) /= (~mToPImpl y)) ]
    , def "eq'" [ `(eq') .= `(MkEq eqImpl neqImpl) ]
    ]

  ------------------------------------
  --- POLY TO POLY CAST DERIVATION ---
  ------------------------------------

  ||| Generate specialised to polymorphic type conversion function signature
  mkPToMImplSig :
    UniResults ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    TTImp
  mkPToMImplSig _ mt =
    forallMTArgs $ arg t.fullInvocation .-> t.specInvocation

  ||| Generate specialised to polymorphic type conversion function clause
  ||| for given constructor
  mkPToMImplClause :
    UnificationResult ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    (pCon : Con) ->
    (0 _ : ConArgsNamed pCon) =>
    (mCon : Con) ->
    (0 _ : ConArgsNamed mCon) =>
    ConMeta ->
    Nat ->
    Clause
  mkPToMImplClause ur _ con mcon meta _ =
    mapClause transMachineVars $
      var "pToMImpl" .$ con.apply bindVar
        (substituteVariables
          (fromList $ argsToBindMap $ con.args) <$> ur.fullResult)
      .= (substituteVariables meta.pToMRenames $ mcon.apply var ur.fullResult)

  ||| Generate specialised to polymorphic type conversion function declarations
  mkPToMImplDecls :
    UniResults ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    TypeMeta ->
    List Decl
  mkPToMImplDecls urs mt meta = do
    let clauses = map2UConsN mkPToMImplClause urs mt meta
    [ def "pToMImpl" clauses
    ]

  ||| Generate specialised to polymorphic cast signature
  mkPToMSig : (mt : TypeInfo) -> (0 _ : AllTyArgsNamed mt) => TTImp
  mkPToMSig mt = do
    forallMTArgs $ `(Cast ~(t.fullInvocation) ~(t.specInvocation))

  ||| Generate specialised to polymorphic cast declarations
  mkPToMDecls : (mt : TypeInfo) -> (0 _ : AllTyArgsNamed mt) => List Decl
  mkPToMDecls mt =
    [ def "pToM" [ (var "pToM") .= `(MkCast pToMImpl)]
    ]

  -----------------------------
  --- FROMSTRING DERIVATION ---
  -----------------------------

  mkFromStringDecls :
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    List Decl
  mkFromStringDecls ti = do
    let pToMImpl = var $ inGenNS t "pToMImpl"
    [ def "fromStringImpl"
      [ `(fromStringImpl @{fs} s) .= `(~pToMImpl $ fromString @{fs} s) ]
    , def "fromString'"
        [ `(fromString' @{fs}) .= `(MkFromString $ ~(var $ inGenNS t "fromStringImpl") @{fs}) ]
    ]

  ----------------------
  --- NUM DERIVATION ---
  ----------------------

  mkNumDecls :
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    List Decl
  mkNumDecls ti = do
    let pToMImpl = var $ inGenNS t "pToMImpl"
    let mToPImpl = var $ inGenNS t "mToPImpl"
    [ def "numImpl"
      [ `(numImpl @{fs} s) .= `(~pToMImpl $ Num.fromInteger @{fs} s) ]
    , def "plusImpl"
        [ `(plusImpl @{fs} a b ) .= `(~pToMImpl $ (+) @{fs} (~mToPImpl a) (~mToPImpl b)) ]
    , def "starImpl"
        [ `(starImpl @{fs} a b ) .= `(~pToMImpl $ (*) @{fs} (~mToPImpl a) (~mToPImpl b)) ]
    , def "num'"
        [ `(num' @{fs}) .=
            `(MkNum
              (~(var $ inGenNS t "plusImpl") @{fs})
              (~(var $ inGenNS t "starImpl") @{fs})
              (~(var $ inGenNS t "numImpl") @{fs}))
        ]
    ]

  ------------------------------------
  --- SPECIALISED TYPE DECLARATION ---
  ------------------------------------

  ||| Generate declarations for given task, unification results, and specialised type
  specDecls : MonadLog m => UniResults -> (mt : TypeInfo) -> (0 _ : AllTyArgsNamed mt) => TypeMeta -> m $ List Decl
  specDecls uniResults specTy specMeta = do
    let specTySig = mkSpecTySig
    let specTyDecl = specTy.decl
    logPoint DetailedDebug "specialiseData.specDecls.specTy.sig" [specTy] $ show mkSpecTySig
    logPoint DetailedDebug "specialiseData.specDecls.specTy" [specTy] $ show specTyDecl
    let mToPImplClaim = mkMToPImplClaim
    let mToPImplDecls = mkMToPImplDecls uniResults specTy specMeta
    logPoint DetailedDebug "specialiseData.specDecls.mToPImpl.sig" [specTy] $ show mToPImplClaim
    logPoint DetailedDebug "specialiseData.specDecls.mToPImpl" [specTy] $ show mToPImplDecls
    let mToPClaim = mkMToPClaim
    let mToPDecls = mkMToPDecls specTy
    logPoint DetailedDebug "specialiseData.specDecls.mToP.sig" [specTy] $ show mToPClaim
    logPoint DetailedDebug "specialiseData.specDecls.mToP" [specTy] $ show mToPDecls
    let castInjDecls = mkCastInjDecls uniResults specTy specMeta
    logPoint DetailedDebug "specialiseData.specDecls.castInj" [specTy] $ show castInjDecls
    let decEqClaims : List Decl = [ mkDecEqImplClaim, mkDecEqClaim ]
    let decEqDecls = mkDecEqDecls uniResults specTy
    logPoint DetailedDebug "specialiseData.specDecls.decEq.sig" [specTy] $ show decEqClaims
    logPoint DetailedDebug "specialiseData.specDecls.decEq" [specTy] $ show decEqDecls
    let showClaims = mkShowClaims
    let showDecls = mkShowDecls uniResults specTy
    logPoint DetailedDebug "specialiseData.specDecls.show.sig" [specTy] $ show showClaims
    logPoint DetailedDebug "specialiseData.specDecls.show" [specTy] $ show showDecls
    let eqClaims = mkEqClaims
    let eqDecls = mkEqDecls uniResults specTy
    logPoint DetailedDebug "specialiseData.specDecls.eq.sig" [specTy] $ show eqClaims
    logPoint DetailedDebug "specialiseData.specDecls.eq" [specTy] $ show eqDecls
    let pToMImplClaim = mkPToMImplClaim
    let pToMImplDecls = mkPToMImplDecls uniResults specTy specMeta
    logPoint DetailedDebug "specialiseData.specDecls.pToMImpl.sig" [specTy] $ show pToMImplClaim
    logPoint DetailedDebug "specialiseData.specDecls.pToMImpl" [specTy] $ show pToMImplDecls
    let pToMClaim = mkPToMClaim
    let pToMDecls = mkPToMDecls specTy
    logPoint DetailedDebug "specialiseData.specDecls.pToM.sig" [specTy] $ show pToMClaim
    logPoint DetailedDebug "specialiseData.specDecls.pToM" [specTy] $ show pToMDecls
    let fromStringClaims = mkFromStringClaims
    let fromStringDecls = mkFromStringDecls specTy
    logPoint DetailedDebug "specialiseData.specDecls.fromString.sig" [specTy] $ show fromStringClaims
    logPoint DetailedDebug "specialiseData.specDecls.fromString" [specTy] $ show fromStringDecls
    let numClaims = mkNumClaims
    let numDecls = mkNumDecls specTy
    logPoint DetailedDebug "specialiseData.specDecls.num.sig" [specTy] $ show numClaims
    logPoint DetailedDebug "specialiseData.specDecls.num" [specTy] $ show numDecls
    let anyUndecided = any isUndecided uniResults
    let sClaims =
        [ mToPImplClaim
        , mToPClaim
        ] ++ join
          [ decEqClaims
          , showClaims
          , eqClaims
          ]
    let dClaims =
        [ pToMImplClaim
        , pToMClaim
        ] ++ join
          [ fromStringClaims
          , numClaims
          ]
    let claims = sClaims ++ if anyUndecided then [] else dClaims
    logPoint DetailedDebug "specialiseData.specDecls.claims" [specTy] $ show claims
    let decidedDecls =
      [ pToMImplDecls
      , pToMDecls
      , fromStringDecls
      , numDecls
      ]
    let onFull : List Decl =
      if anyUndecided
          then []
          else join decidedDecls

    pure $ singleton $ INamespace EmptyFC (MkNS [ show t.resultName ]) $
      join
        [ [ mkSpecTySig ]
        , claims
        , [ specTyDecl ]
        , mToPImplDecls
        , mToPDecls
        , castInjDecls
        , decEqDecls
        , showDecls
        , eqDecls
        , onFull
        ]

---------------------------
--- DATA SPECIALISATION ---
---------------------------

||| Perform a specialisation for a given type name, kind and content expressions
|||
||| In order to generate a specialised type declaration equivalent to the following type alias:
||| ```
||| VF : Nat -> Type
||| VF n = Fin n
||| ```
||| ...you may use this function as follows:
||| ```
||| specialiseDataRaw `{VF} `(Nat -> Type) `(\n => Fin n)
||| ```
export
specialiseDataRaw :
  Monad m =>
  (nsProvider : NamespaceProvider m) =>
  (unifier : CanUnify m) =>
  MonadLog m =>
  MonadError SpecialisationError m =>
  (namesInfo : NamesInfoInTypes) =>
  SpecialisationParams =>
  (resultName : Name) ->
  (resultKind : TTImp) ->
  (resultContent : TTImp) ->
  m (TypeInfo, List Decl)
specialiseDataRaw resultName resultKind resultContent = do
  let resultKind = mapTTImp cleanupHoleAutoImplicitsImpl $ cleanupNamedHoles resultKind
  let resultContent = mapTTImp cleanupHoleAutoImplicitsImpl $ cleanupNamedHoles resultContent
  task <- getTask resultName resultKind resultContent
  logPoint DetailedDebug "specialiseData" [task.polyTy] "Specialisation task: \{show task}"
  uniResults <- sequence $ mapCons task $ unifyCon task
  (Element specTy specTyNamed, specMeta) <- mkSpecTy task uniResults
  decls <- specDecls task uniResults specTy specMeta
  pure (specTy, decls)

typeDPair : List Arg -> TTImp
typeDPair [] = `(Type)
typeDPair (x :: xs) = do
  let aName = fromMaybe "" x.name
  let aTyName = fromString "\{aName}^ty"
  let tyArg = MkArg MW ExplicitArg (Just aTyName) `(Type)
  let tyVar = var aTyName
  let valArg = MkArg MW ExplicitArg (Just aName) tyVar
  `(DPair Type ~(lam tyArg `(DPair ~tyVar ~(lam valArg $ typeDPair xs))))

valDPair : SortedMap Name String ->  List Arg -> TTImp -> TTImp
valDPair n2s [] x = x
valDPair n2s (x :: xs) y = do
  let aName = fromMaybe "" x.name
  let aTyName = fromString "\{aName}^ty"
  let tyVar = var aTyName
  let valVar = var aName
  let valHole = fromMaybe `(?) $ hole <$> lookup aName n2s
  `(MkDPair ~(x.type) ~(iLet MW aName x.type valHole `(MkDPair ~valVar ~(valDPair n2s xs y))))

unholeImpl : SortedMap String Name -> TTImp -> TTImp
unholeImpl s2n (IHole fc holeName) =
  case lookup holeName s2n of
      Just vn => var vn
      Nothing => IHole fc holeName
unholeImpl s2n t = t

unhole : SortedMap String Name -> TTImp -> TTImp
unhole s2n = mapTTImp (unholeImpl s2n)

unBadHoleImpl : TTImp -> TTImp
unBadHoleImpl (IHole fc "_") = Implicit fc False
unBadHoleImpl t = t

unBadHole : TTImp -> TTImp
unBadHole = mapTTImp unBadHoleImpl

unMkDPair : TTImp -> List TTImp
unMkDPair (IApp _ (IApp _ (INamedApp _ (INamedApp _ (IVar _ "Builtin.DPair.MkDPair") _ _) _ _) dl) dr) =
  dl :: unMkDPair dr
unMkDPair _ = []

decodeDPair : Elaboration m => List Arg -> List TTImp -> m (List Arg)
decodeDPair [] _ = pure []
decodeDPair (a :: as) (aT :: _ :: ts) = pure $ ({type := aT} a) :: !(decodeDPair as ts)
decodeDPair _ _ = fail "INTERNAL ERROR: Failed during lambda normalisation"

genAliases : Elaboration m => List Arg -> m (SortedMap Name String, SortedMap String Name)
genAliases = foldlM genAImpl (empty, empty)
  where
    genAImpl :
      (SortedMap Name String, SortedMap String Name) ->
      Arg ->
      m (SortedMap Name String, SortedMap String Name)
    genAImpl (n2s, s2n) a = do
      randN <- genSym "lamArg"
      let s = show randN
      let n = fromMaybe "" a.name
      pure (insert n s n2s, insert s n s2n)

export
normaliseTask : Elaboration m => List Arg -> TTImp -> m (TTImp, TTImp)
normaliseTask lamArgs lamRhs = do
  (n2s, s2n) <- genAliases lamArgs
  nT : Type <- check $ unBadHole $ typeDPair lamArgs
  nV : nT <- check $ unBadHole $ valDPair n2s lamArgs lamRhs
  nVQ <- quote nV
  newArgs <- decodeDPair lamArgs $ unMkDPair $ unBadHole $ unhole s2n nVQ
  let newLamTy = piAll `(Type) newArgs
  let newLam = foldr lam lamRhs newArgs
  pure (newLamTy, newLam)

export
specialiseDataArgs :
  Elaboration m =>
  (nsProvider : NamespaceProvider m) =>
  (unifier : CanUnify m) =>
  MonadLog m =>
  MonadError SpecialisationError m =>
  (namesInfo : NamesInfoInTypes) =>
  SpecialisationParams =>
  (resultName : Name) ->
  (lambdaArgs : List Arg) ->
  (lambdaRHS : TTImp) ->
  m (TypeInfo, List Decl)
specialiseDataArgs resultName fvArgs lambdaRHS =
  uncurry (specialiseDataRaw resultName) =<< normaliseTask fvArgs lambdaRHS

||| Perform a specialisation for a given type name and content lambda
|||
||| In order to generate a specialised type declaration equivalent to the following type alias:
||| ```
||| VF : Nat -> Type
||| VF n = Fin n
||| ```
||| ...you may use this function as follows:
||| ```
||| specialiseData `{VF} $ \n => Fin n
||| ```
export
specialiseDataLam :
  -- TaskLambda taskT =>
  Monad m =>
  Elaboration m =>
  (nsProvider : NamespaceProvider m) =>
  (unifier : CanUnify m) =>
  MonadError SpecialisationError m =>
  (namesInfo : NamesInfoInTypes) =>
  SpecialisationParams =>
  (resultName : Name) ->
  (0 task : taskT) ->
  m (TypeInfo, List Decl)
specialiseDataLam resultName task = do
  -- Quote spec lambda type
  resultKind <- quote taskT
  -- Quote spec lambda
  resultContent <- quote task
  specialiseDataRaw resultName resultKind resultContent


||| Perform a specialisation for a given type name and content lambda,
||| returning a list of declarations and failing on error
|||
||| In order to generate a specialised type declaration equivalent to the following type alias:
||| ```
||| VF : Nat -> Type
||| VF n = Fin n
||| ```
||| ...you may use this function as follows:
||| ```
||| specialiseDataLam'' `{VF} $ \n => Fin n
||| ```
export
specialiseDataLam'' :
  Elaboration m =>
  (nsProvider : NamespaceProvider m) =>
  (unifier : CanUnify m) =>
  SpecialisationParams =>
  -- TaskLambda taskT =>
  Name ->
  (0 task: taskT) ->
  m $ List Decl
specialiseDataLam'' resultName task = do
  tq <- quote task
  nit <- getNamesInfoInTypes' tq
  Right (specTy, decls) <-
    runEitherT {m} {e=SpecialisationError} $
      specialiseDataLam resultName task
  | Left err => fail "Specialisation error: \{show err}"
  pure decls

||| Perform a specialisation for a given type name and content lambda,
||| declaring the results and failing on error
|||
||| In order to declare a specialised type declaration equivalent to the following type alias:
||| ```
||| VF : Nat -> Type
||| VF n = Fin n
||| ```
||| ...you may use this function as follows:
||| ```
||| %runElab specialiseDataLam' `{VF} $ \n => Fin n
||| ```
export
specialiseDataLam' :
  Elaboration m =>
  (nsProvider : NamespaceProvider m) =>
  (unifier : CanUnify m) =>
  SpecialisationParams =>
  -- TaskLambda taskT =>
  Name ->
  (0 task: taskT) ->
  m ()
specialiseDataLam' resultName task =
  specialiseDataLam'' resultName task >>= declare

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

-- export
-- %defaulthint
-- CurrentNS : Elaboration m => NamespaceProvider m
-- CurrentNS = MkNSProvider $ do
--     NS nsn _ <- inCurrentNS ""
--     | _ => fail "Internal error: inCurrentNS did not return NS"
--     pure nsn

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

||| Given a list of arguments, generate a list of aliases for them
transformArgNames' : (f : Name -> Name) -> (as : List Arg) -> (0 _ : All IsNamedArg as) => List (Name, Name)
transformArgNames' _ [] = []
transformArgNames' f (x :: xs) @{_ :: _} =
  (argName x, f $ Expr.argName x) :: transformArgNames' f xs

||| Given a list of arguments, generate a list of aliased arguments
||| and a list of aliases
transformArgNames :
  (f : Name -> Name) ->
  (as : List Arg) ->
  (0 _ : All IsNamedArg as) =>
  (Subset (List Arg) (All IsNamedArg), List (Name, Name))
transformArgNames f as = do
  let aliases = transformArgNames' f as
  (applyArgAliases as aliases empty, aliases)

||| Given a list of aliased argument pairs, generate a list of equality type
||| for each pair
mkEqualsTuple : List (Subset Arg IsNamedArg, Subset Arg IsNamedArg) -> TTImp
mkEqualsTuple [] = `(MkUnit)
mkEqualsTuple [(Element a1 _, Element a2 _)] =
  `(~(var $ argName a1) ~=~ ~(var $ argName a2))
mkEqualsTuple ((Element a1 _, Element a2 _) :: as) =
  `(Pair (~(var $ argName a1) ~=~ ~(var $ argName a2)) ~(mkEqualsTuple as))

||| Given a list of aliased argument pairs [(a, b), ...], generate a series of
||| named applications: (... {a=a} {b=a})
mkDoubleBinds : SnocList (Arg, Arg) -> TTImp -> TTImp
mkDoubleBinds [<] t = t
mkDoubleBinds (as :< (a1, a2)) t =
  case (a1.name, a2.name) of
    (Just a1n, Just a2n) =>
      mkDoubleBinds as t .! (a1n, bindVar a1n) .! (a2n, bindVar a1n)
    _ => mkDoubleBinds as t

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
tupleOfN (S n) t = `(MkPair ~(t) ~(tupleOfN n t))

||| Map all unmapped variables from the list to their aliases
mergeAliases : SortedMap Name TTImp -> List (Name, Name) -> SortedMap Name TTImp
mergeAliases m = mergeWith (Prelude.curry fst) m . fromList . map (mapSnd var)

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

||| Create a binding application of aliased arguments
||| binding everything to `(_)
aliasedAppBind : SnocList (Name, Name) -> TTImp -> TTImp
aliasedAppBind [<] t = t
aliasedAppBind (xs :< (n, an)) t = aliasedAppBind xs t .! (an, `(_))


||| Create a non-binding application of aliased arguments
aliasedApp : SnocList (Name, Name) -> TTImp -> TTImp
aliasedApp [<] t = t
aliasedApp (xs :< (n, an)) t = aliasedApp xs t .! (n, var an)

---------------------
--- TASK ANALYSIS ---
---------------------

||| Given a list of arguments and a sorted set of names,
||| assert that every argument's name is in that set
checkArgsUse :
  MonadError SpecialisationError m =>
  List Arg ->
  SortedSet Name ->
  m ()
checkArgsUse [] _ = pure ()
checkArgsUse (x :: xs) t = do
  let Just n = x.name
  | _ => checkArgsUse xs t
  if contains n t
    then checkArgsUse xs t
    else throwError UnusedVarError

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
  let specInvocation = reAppAny (var (inGenNSImpl currentNs resultName resultName)) $ ttArgs.appsWith @{ttArgsNamed} var empty
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

allL2V : (l : List t) -> (0 pr : All p l) => Subset (Vect (length l) t) (All p)
allL2V [] = Element [] []
allL2V (x :: xs) @{p :: ps} = do
  let Element xs' ps' = allL2V xs @{ps}
  Element (x :: xs') (p :: ps')

0 snocLengthEqS : (prev : List a) -> (new : a) -> length (snoc prev new) = S (length prev)
snocLengthEqS [] _ = Refl
snocLengthEqS (x :: xs) y = rewrite snocLengthEqS xs y in Refl

0 snocAll : {0 prev : Vect _ _} -> All IsNamedArg prev -> (new : Arg) -> IsNamedArg new -> All IsNamedArg (snoc prev new)
snocAll [] new y = [y]
snocAll (y :: ys) new z = y :: snocAll ys new z

0 snocAllL : {0 prev : List _} -> All IsNamedArg prev -> (new : Arg) -> IsNamedArg new -> All IsNamedArg (snoc prev new)
snocAllL [] new y = [y]
snocAllL (y :: ys) new z = y :: snocAllL ys new z

snocAll2L : (sl : SnocList Arg) -> (0 _ : All IsNamedArg sl) -> Subset (List Arg) (All IsNamedArg)
snocAll2L [<] [<] = Element [] []
snocAll2L (sx :< x) (sy :< y) = do
  let Element xs ys = snocAll2L sx sy
  Element (snoc xs x) (snocAllL ys x y)

record RecursionSearchState where
  constructor MkRSS
  castRenames : SortedMap Name TTImp
  pToMRenames : SortedMap Name TTImp
  areArgsRecursive : SnocList Bool
  argsForUnifier : Subset (Vect (length areArgsRecursive) Arg) (All IsNamedArg)
  argsOutput : Subset (SnocList Arg) (All IsNamedArg)

record ArgMeta where
  constructor MkAMeta
  isResursiveArg : Bool

-- Workaround for possible compiler bug
isRA : ArgMeta -> Bool
isRA (MkAMeta True) = True
isRA (MkAMeta False) = False

record ConMeta where
  constructor MkCMeta
  argMeta : List ArgMeta
  mToPRenames : SortedMap Name TTImp
  pToMRenames : SortedMap Name TTImp

hasRecursiveArgs : ConMeta -> Bool
hasRecursiveArgs = any isRA . argMeta

countRecursiveArgs : ConMeta -> Nat
countRecursiveArgs = count isRA . argMeta

recursiveArgNames : Con -> ConMeta -> List Name
recursiveArgNames con meta = do
  let recursiveArgPairs = List.filter (isRA . snd) $ zip con.args meta.argMeta
  fromMaybe "" . name . fst <$> recursiveArgPairs

record TypeMeta where
  constructor MkTyMeta
  conMeta : List ConMeta

tupleOf : List TTImp -> TTImp
tupleOf [] = `(())
tupleOf [x] = x
tupleOf (x :: xs) = `(MkPair ~x ~(tupleOf xs))

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
  unifyCon :
    MonadLog m =>
    (unifier : CanUnify m) =>
    (con : Con) ->
    (0 conN : ConArgsNamed con) =>
    m UnificationVerdict
  unifyCon con = logBounds Debug "specialiseData.unifyCon" [t.polyTy, con] $ do
    let Element ca _ = allL2V con.args @{conArgsNamed}
    let Element ta _ = allL2V t.tqArgs @{t.tqArgsNamed}
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
  mkSpecArg :
    (ur : UnificationResult) ->
    Fin (ur.uniDg.freeVars) ->
    (Subset Arg IsNamedArg)
  mkSpecArg ur fvId = do
    let fvData = index fvId ur.uniDg.fvData
    let fromLambda = finToNat fvId >= ur.task.lfv
    let rig = if fromLambda then M0 else fvData.rig
    let piInfo = if fromLambda && (fvData.piInfo == ExplicitArg) then ImplicitArg else fvData.piInfo
    Element (MkArg rig piInfo (Just fvData.name) fvData.type) ItIsNamed

  getVar : TTImp -> Maybe Name
  getVar (IVar _ n) = Just n
  getVar _ = Nothing

  findRecursiveApps :
    Monad m =>
    CanUnify m =>
    MonadLog m =>
    NamesInfoInTypes =>
    RecursionSearchState -> Subset Arg IsNamedArg -> m RecursionSearchState
  findRecursiveApps rss (Element thisArg thisArgNamed) = do
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
            (Element (snoc argsForUni thisArg) (snocAll %search thisArg thisArgNamed))
            (Element (argsOut :< outArg) (%search :< outArgNamed))
    let Element ta _ = allL2V t.tqArgs @{t.tqArgsNamed}
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
            (Element (snoc argsForUni thisArg) (snocAll %search thisArg thisArgNamed))
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
            (Element (snoc argsForUni thisArg) (snocAll %search thisArg thisArgNamed))
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
    rssRhs <- foldlM findRecursiveApps (MkRSS empty empty [<] (Element [] []) (Element [<] [<])) specArgs
    let (MkRSS cRename pToMRenames argsAreRecursive' _ (Element outArgs' outArgsNamed')) = rssRhs
    let Element outArgs outArgsNamed = snocAll2L outArgs' outArgsNamed'
    let conMeta = MkCMeta (MkAMeta <$> toList argsAreRecursive') cRename pToMRenames
    pure $ (MkCon
      { name = inGenNS t $ n
      , args = outArgs
      , type = substituteVariables cRename tyRet
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

  recCastInj : Name -> Name -> TTImp
  recCastInj p1 p2 = `(~(var $ inGenNS t $ "castInjImpl") $ trans ~(var p1) $ sym ~(var p2))

  amrContent : Arg -> ArgMeta -> (Name -> Name) -> TTImp
  amrContent a (MkAMeta False) _ = `(_)
  amrContent a (MkAMeta True) alias = bindVar $ alias $ fromMaybe "" a.name

  argMaybeRecursive : (Name -> Name) -> (Arg, ArgMeta) -> AnyApp
  argMaybeRecursive alias (a@(MkArg count ImplicitArg name type), am) = NamedApp (fromMaybe "" name) $ amrContent a am alias
  argMaybeRecursive alias (a@(MkArg count ExplicitArg name type), am) = PosApp $ amrContent a am alias
  argMaybeRecursive alias (a@(MkArg count AutoImplicit name type), am) = NamedApp (fromMaybe "" name) $ amrContent a am alias
  argMaybeRecursive alias (a@(MkArg count (DefImplicit x) name type), am) = NamedApp (fromMaybe "" name) $ amrContent a am alias

  conOnlyRecursivesAliased : Con -> ConMeta -> (Name -> Name) -> TTImp
  conOnlyRecursivesAliased con meta alias =
    reAppAny (var con.name) $ argMaybeRecursive alias <$> zip con.args meta.argMeta

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

  withManyUnders : Nat -> TTImp -> TTImp
  withManyUnders 0 x = x
  withManyUnders (S n) x = withManyUnders n `(~x | _)

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

  mkInitialLhs : Con -> ConMeta -> TTImp
  mkInitialLhs con meta = do
    let lhsCon = conOnlyRecursivesAliased con meta $ prependS "lhs^"
    let rhsCon = conOnlyRecursivesAliased con meta $ prependS "rhs^"
    var "castInjImpl" .! ("castInj^x", lhsCon) .! ("castInj^y", rhsCon) .$ bindVar "prf"

  mkRecArgClauses : List Name -> TTImp -> Clause -> Clause
  mkRecArgClauses [] exLhs inner = inner
  mkRecArgClauses (x :: xs) exLhs inner = mkArgWithClause x exLhs $ mkRecArgClauses xs `(~exLhs | _ | _) inner

  mkCastInjClause' :
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
  mkCastInjClause' ur mt _ con meta n = do
    if not (hasRecursiveArgs meta)
      then do
        let emptyCon = con.apply (\_ => `(_)) empty
        (var "castInjImpl") .! ("castInj^x", emptyCon) .! ("castInj^y", emptyCon) .$ `(Refl) .= `(Refl)
      else do
        let finalClause = mkFinalClause con meta
        let recNames = recursiveArgNames con meta
        let initLhs = mkInitialLhs con meta
        mkRecArgClauses recNames initLhs finalClause

  ||| Make a clause for the cast injectivity proof
  mkCastInjClause :
    (tal1, tal2 : (List Arg, List (Name, Name))) ->
    (n1, n2 : Name) ->
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
  mkCastInjClause (ta1, tam1) (ta2, tam2) n1 n2 ur mt _ con meta n = do
    let 0 _ = conArgsNamed @{mcn}
    let (Element a1 _, am1) = transformArgNames (prependS "lhs^") con.args
    let (Element a2 _, am2) = transformArgNames (prependS "rhs^") con.args
    let am1' = fromList $ mapSnd (const `(_)) <$> am1
    let am2' = fromList $ mapSnd (const `(_)) <$> am2
    let ures1 = substituteVariables am1' <$> ur.fullResult
    let ures2 = substituteVariables am2' <$> ur.fullResult
    let bta1 = aliasedAppBind (cast tam1) `(castInjImpl)
    let bta2 = aliasedAppBind (cast tam2) bta1
    let lhsCon = con.apply bindVar $ am1'
    let rhsCon = con.apply bindVar $ am1'
    let patRhs : TTImp
        patRhs = case (length a1) of
          0 => `(Refl)
          _ => (var $ inGenNS t $ fromString $ "mCong\{show n}") .$
                ((var $ inGenNS t $ fromString $ "mInj\{show n}") .$ var "r")
    bta2 .! (n1, lhsCon) .! (n2, rhsCon) .$ bindVar "r" .= patRhs

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
    let castInjImplClauses = map2UConsN (mkCastInjClause') ur ti meta
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
    let specTyDecl = specTy.decl
    logPoint DetailedDebug "specialiseData.specDecls.specTy" [specTy] $ show specTyDecl
    let mToPImplDecls = mkMToPImplDecls uniResults specTy specMeta
    logPoint DetailedDebug "specialiseData.specDecls.mToPImpl" [specTy] $ show mToPImplDecls
    let mToPDecls = mkMToPDecls specTy
    logPoint DetailedDebug "specialiseData.specDecls.mToP" [specTy] $ show mToPDecls
    let castInjDecls = mkCastInjDecls uniResults specTy specMeta
    logPoint DetailedDebug "specialiseData.specDecls.castInj" [specTy] $ show castInjDecls
    let decEqDecls = mkDecEqDecls uniResults specTy
    logPoint DetailedDebug "specialiseData.specDecls.decEq" [specTy] $ show decEqDecls
    let showDecls = mkShowDecls uniResults specTy
    logPoint DetailedDebug "specialiseData.specDecls.show" [specTy] $ show showDecls
    let eqDecls = mkEqDecls uniResults specTy
    logPoint DetailedDebug "specialiseData.specDecls.eq" [specTy] $ show eqDecls
    let pToMImplDecls = mkPToMImplDecls uniResults specTy specMeta
    logPoint DetailedDebug "specialiseData.specDecls.pToMImpl" [specTy] $ show pToMImplDecls
    let pToMDecls = mkPToMDecls specTy
    logPoint DetailedDebug "specialiseData.specDecls.pToM" [specTy] $ show pToMDecls
    let fromStringDecls = mkFromStringDecls specTy
    logPoint DetailedDebug "specialiseData.specDecls.fromString" [specTy] $ show fromStringDecls
    let numDecls = mkNumDecls specTy
    logPoint DetailedDebug "specialiseData.specDecls.num" [specTy] $ show numDecls
    let anyUndecided = any isUndecided uniResults
    let claims = standardClaims ++ if anyUndecided then [] else decidedClaims
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

-------------------------------------
--- SPECIALISATION TASK INTERFACE ---
-------------------------------------

||| Valid task lambda interface
|||
||| Auto-implemented by any Type or any function that returns Type.
-- export
-- interface TaskLambda (t : Type) where
--
-- export
-- TaskLambda Type
--
-- %hint
-- export
-- tlImplTy : (a : Type) -> TaskLambda a
--
-- export
-- TaskLambda b => TaskLambda (a -> b)
--
-- export
-- TaskLambda b => TaskLambda (a => b)
--
-- export
-- TaskLambda b => TaskLambda ({_ : a} -> b)
--
-- export
-- {x : _} -> TaskLambda b => TaskLambda ({default x _ : a} -> b)
--
-- export
-- TaskLambda b => TaskLambda ((0 _ : a) -> b)
--
-- export
-- TaskLambda b => TaskLambda ((0 _ : a) => b)
--
-- export
-- TaskLambda b => TaskLambda ({0 _ : a} -> b)
--
-- export
-- {0 x : _} -> TaskLambda b => TaskLambda ({default x 0 _ : a} -> b)
--
-- %hint
-- export
-- tlImpl0 : {a : Type} -> {0 f : a -> Type} -> (x : a) => TaskLambda (f x) => TaskLambda ((x : a) -> f x)
--
-- export
-- {0 f : _ -> _} -> TaskLambda (f a) => TaskLambda (a => f a)
--
-- export
-- {0 f : _ -> _} -> TaskLambda (f a) => TaskLambda ({_: a} -> f a)
--
-- export
-- {x : _} -> {0 f : _ -> _} -> TaskLambda (f a) => TaskLambda ({default x _: a} -> f a)
--
-- export
-- {0 f : _ -> _} -> TaskLambda (f a) => TaskLambda ((0 _ : a) -> f a)
--
-- export
-- {0 f : _ -> _} -> TaskLambda (f a) => TaskLambda ((0 _ : a) => f a)
--
-- export
-- {0 f : _ -> _} -> TaskLambda (f a) => TaskLambda ({0 _: a} -> f a)
--
-- export
-- {0 x : _} -> {0 f : _ -> _} -> TaskLambda (f a) => TaskLambda ({default x 0 _: a} -> f a)


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

export
normaliseTask : Elaboration m => List Arg -> TTImp -> m (TTImp, TTImp)
normaliseTask fvs ret = do
  lamTy : Type <- check $ piAll `(Type) fvs
  lam <- normaliseAs lamTy $ foldr lam ret fvs
  lamTy' <- quote lamTy
  pure (lamTy', lam)

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

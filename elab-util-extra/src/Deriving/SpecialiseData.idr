module Deriving.SpecialiseData

import Control.Monad.Either
import Control.Monad.Error.Either
import Control.Monad.Error.Interface
import Control.Monad.Reader.Tuple
import Control.Monad.Trans
import Data.SnocList
import Data.DPair
import Data.List1
import Data.Vect
import Data.Vect.Quantifiers
import Data.List
import Data.List.Quantifiers
import Data.Either
import Data.SortedMap
import Data.SortedSet
import Data.SortedMap.Dependent
import Decidable.Equality
import Deriving.Show
import Language.Mk
import Language.Reflection.Compat
import Language.Reflection.Compat.Constr
import Language.Reflection.Compat.TypeInfo
import Language.Reflection.Expr
import Language.Reflection.Logging
import Language.Reflection.Unify
import Language.Reflection.VarSubst
import Syntax.IHateParens

%language ElabReflection

%default total

---------------------------------
--- SPECIALISATION ERROR TYPE ---
---------------------------------

||| Specialisation error
export
data SpecialisationError : Type where
  ||| Failed to extract invocation from task
  InvocationExtractionError : SpecialisationError
  ||| Failed to extract polymorphic type name from task
  TaskTypeExtractionError   : SpecialisationError
  ||| Unused variable
  UnusedVarError            : SpecialisationError
  ||| Partial specification
  PartialSpecError          : SpecialisationError

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
interface NamespaceProvider (0 m : Type -> Type) where
  constructor MkNSProvider
  provideNS : m Namespace

export %defaulthint
CurrentNS : Elaboration m => NamespaceProvider m
CurrentNS = MkNSProvider $ do
    NS nsn _ <- inCurrentNS ""
    | _ => fail "Internal error: inCurrentNS did not return NS"
    pure nsn

export
Monad m => MonadTrans t => NamespaceProvider m => NamespaceProvider (t m) where
  provideNS = lift provideNS

export
inNS : Elaboration m => Namespace -> NamespaceProvider m
inNS ns = MkNSProvider $ pure ns

||| Prepend namespace into which everything is generated to name
inGenNS : SpecTask -> Name -> Name
inGenNS task n = do
  let MkNS tns = task.currentNs
  let newNS =
    case n of
       (NS (MkNS subs) n) => subs
       n => []
  NS (MkNS $ newNS ++ show task.resultName :: tns) $ dropNS n

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

||| Given a list of arguments, generate a list of aliases for them
genAliases' : Elaboration m => (as : List Arg) -> (0 _ : All IsNamedArg as) => m $ List (Name, Name)
genAliases' [] = pure []
genAliases' @{_} (x :: xs) @{_ :: _} = do
  MN _ gn <- genSym $ show $ Expr.argName x
  | _ => fail "Intenal specialiser error: genSym returned non-MS name"
  pure $ (argName x, UN $ Basic $ show (Expr.argName x) ++ show gn) :: !(genAliases' xs)

||| Given a list of arguments, generate a list of aliased arguments
||| and a list of aliases
genArgAliases :
  Elaboration m =>
  (as : List Arg) ->
  (0 _ : All IsNamedArg as) =>
  m (Subset (List Arg) (All IsNamedArg), List (Name, Name))
genArgAliases as = do
  aliases <- genAliases' as
  pure (applyArgAliases as aliases empty, aliases)

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

||| A tuple value of multiple repeating expressons
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

||| Get all the information needed for specialisation from task
getTask :
  Monad m =>
  Elaboration m =>
  NamespaceProvider m =>
  MonadError SpecialisationError m =>
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
  | _ => fail "Internal error: lambda has unnamed arguments"
  -- Create aliases for spec lambda's arguments and perform substitution
  (Element tqArgs tqArgsNamed, tqAlias) <- genArgAliases tqArgs
  let tqRet = substituteVariables (fromList $ mapSnd var <$> tqAlias) tqRet
  let (ttArgs, _) = unPi resultKind
  -- Check for partial application in spec
  let True = (length tqArgs == length ttArgs)
  | _ => throwError PartialSpecError
  -- Prove that all spec lambda type's arguments are named
  let Yes ttArgsNamed = all isNamedArg ttArgs
  | _ => fail "Internal error: lambda type has unnamed arguments"
  -- Apply aliasing to spec lambda type's info
  let Element ttArgs ttArgsNamed = applyArgAliases ttArgs tqAlias empty
  -- Get current namespace
  currentNs <- provideNS
  -- Get polymorphic type's info
  polyTy <- getInfo' typeName
  -- Prove all its arguments/constructors/constructor arguments are named
  polyTyNamed <- ensureTyArgsNamed polyTy
  pure $ MkSpecTask
    { tqArgs
    , tqRet
    , tqArgsNamed
    , ttArgs
    , ttArgsNamed
    , currentNs
    , resultName
    , fullInvocation = tqRet --- TODO: intelligent full invocation
    , polyTy
    , polyTyNamed
    }

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
         r) ->
    UniResults ->
    List r
  mapUCons f rs = do
    let adp = pushIn t.polyTy.cons t.polyTyNamed.tyConArgsNamed
    let f' : List (Subset Con ConArgsNamed) -> UniResults -> List r
        f' (Element con _ :: xs) (Success res :: ys) = f res con :: f' xs ys
        f' (_ :: xs)             (_ :: ys)           = f' xs ys
        f' _ _ = []
    f' adp rs

  ||| Run monadic operation on all pairs of specified and polymorphic constructors
  map2UConsN :
    (f : UnificationResult ->
         (mt : TypeInfo) ->
         (0 _ : AllTyArgsNamed mt) =>
         (con : Con) ->
         (0 _ : ConArgsNamed con) =>
         (mcon : Con) ->
         (0 _ : ConArgsNamed mcon) =>
         Nat ->
         r) ->
    UniResults ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    List r
  map2UConsN f rs mt @{mtp} = do
    let p1 = pushIn t.polyTy.cons t.polyTyNamed.tyConArgsNamed
    let p2 = pushIn mt.cons mtp.tyConArgsNamed
    f' 0 p1 p2 rs
    where
      f' :
        Nat ->
        List (Subset Con ConArgsNamed) ->
        List (Subset Con ConArgsNamed) ->
        UniResults ->
        List r
      f' n (Element con _ :: xs) (Element mcon _ :: ys) (Success res :: zs) =
        f res mt con mcon n :: f' (S n) xs ys zs
      f' n (_             :: xs)                    ys  (_:: zs) =
        f' n xs ys zs
      f' _ _ _ _ = []

  -------------------------------
  --- CONSTRUCTOR UNIFICATION ---
  -------------------------------

  ||| Run unification for a given polymorphic constructor
  unifyCon :
    Elaboration m =>
    (unifier : CanUnify m) =>
    (con : Con) ->
    (0 conN : ConArgsNamed con) =>
    m UnificationVerdict
  unifyCon con = logBounds "specialiseData.unifyCon" [t.polyTy, con] $ do
    let Element ca _ = allL2V con.args @{conArgsNamed}
    let Element ta _ = allL2V t.tqArgs @{t.tqArgsNamed}
    let uniTask =
      MkUniTask {lfv=_} ca con.type
                {rfv=_} ta t.fullInvocation
    logPoint {level=DetailedTrace} "specialiseData.unifyCon" [t.polyTy, con] "Unifier task: \{show uniTask}"
    uniRes <- unify uniTask
    logPoint {level=DetailedTrace} "specialiseData.unifyCon" [t.polyTy, con] "Unifier output: \{show uniRes}"
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
    (Element (MkArg rig piInfo (Just fvData.name) fvData.type) ItIsNamed)

  ||| Generate a specialised constructor
  mkSpecCon :
    (newArgs : _) ->
    (0 _ : All IsNamedArg newArgs) =>
    UnificationResult ->
    (con : Con) ->
    (0 _ : ConArgsNamed con) =>
    Subset Con ConArgsNamed
  mkSpecCon newArgs ur pCon = do
    let Element args allArgs =
      pullOut $ mkSpecArg ur <$> ur.order
    let typeArgs = newArgs.appsWith var ur.fullResult
    let tyRet = reAppAny (var t.resultName) typeArgs
    MkCon
      { name = inGenNS t $ dropNS pCon.name
      , args
      , type = tyRet
      } `Element` TheyAreNamed allArgs

  ||| Generate a specialised type
  mkSpecTy : UniResults -> Subset TypeInfo AllTyArgsNamed
  mkSpecTy ur = do
    let Element cons consAreNamed =
      pullOut $ mapUCons (mkSpecCon t.ttArgs @{t.ttArgsNamed}) ur
    MkTypeInfo
      { name = inGenNS t t.resultName
      , args = t.ttArgs
      , cons
      } `Element` TheyAllAreNamed t.ttArgsNamed consAreNamed

  ------------------------------------
  --- POLY TO POLY CAST DERIVATION ---
  ------------------------------------

  ||| Generate IPi with implicit type arguments and given return
  forallMTArgs : TTImp -> TTImp
  forallMTArgs = flip (foldr pi) $ makeTypeArgM0 . hideExplicitArg <$> t.ttArgs


  ||| Generate specialised to polimorphic type conversion function signature
  mkMToPImplSig : UniResults -> (mt : TypeInfo) -> (0 _ : AllTyArgsNamed mt) => TTImp
  mkMToPImplSig _ mt =
    forallMTArgs $ arg (mt.apply var empty) .-> t.fullInvocation

  ||| Generate specialised to polimorphic type conversion function clause
  ||| for given constructor
  mkMToPImplClause :
    UnificationResult ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    (pCon : Con) ->
    (0 _ : ConArgsNamed pCon) =>
    (mCon : Con) ->
    (0 _ : ConArgsNamed mCon) =>
    Nat ->
    Clause
  mkMToPImplClause ur _ con mcon _ =
    var "mToPImpl" .$
      mcon.apply bindVar
        (substituteVariables
          (fromList $ argsToBindMap mcon.args) <$> ur.fullResult)
      .= con.apply var ur.fullResult

  ||| Generate specialised to polimorphic type conversion function declarations
  mkMToPImplDecls :
    UniResults ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    List Decl
  mkMToPImplDecls urs mt = do
    let sig = mkMToPImplSig urs mt
    let clauses = map2UConsN mkMToPImplClause urs mt
    [ public' "mToPImpl" sig
    , def "mToPImpl" clauses
    ]

  ||| Generate specialised to polimorphic cast signature
  mkMToPSig : (mt : TypeInfo) -> (0 _ : AllTyArgsNamed mt) => TTImp
  mkMToPSig mt = do
    forallMTArgs $ `(Cast ~(mt.apply var empty) ~(t.fullInvocation))

  ||| Generate specialised to polimorphic cast declarations
  mkMToPDecls : (mt : TypeInfo) -> (0 _ : AllTyArgsNamed mt) => List Decl
  mkMToPDecls mt =
    [ interfaceHint Public "mToP" $ mkMToPSig mt
    , def "mToP" [ (var "mToP") .= `(MkCast mToPImpl)]
    ]

  -----------------------------------
  --- MULTIINJECTIVITY DERIVATION ---
  -----------------------------------
  parameters {auto _ : Elaboration m}
    ||| Derive multiinjectivity for a polymorphic constructor that has a
    ||| specialised equivalent
    mkMultiInjDecl :
      UnificationResult ->
      (mt : TypeInfo) ->
      (0 _ : AllTyArgsNamed mt) =>
      (pCon : Con) ->
      (0 _ : ConArgsNamed pCon) =>
      (mCon : Con) ->
      (0 mn : ConArgsNamed mCon) =>
      Nat ->
      m $ List Decl
    mkMultiInjDecl ur mt con mcon i =
      logBounds "specialiseData.mkMultiInjDecl" [mt, mcon] $ do
        let S _ = length mcon.args
        | _ => pure []
        let n = fromString "mInj\{show i}"
        let 0 _ = conArgsNamed @{mn}
        let Element ourArgs _ = makeArgsImplicit mcon.args
        (Element a1 _, am1) <- genArgAliases ourArgs
        (Element a2 _, am2) <- genArgAliases ourArgs
        let lhsCon = substituteVariables (fromList $ mapSnd var <$> am1) $
                      con.apply var $ mergeAliases ur.fullResult am1
        let rhsCon = substituteVariables (fromList $ mapSnd var <$> am2) $
                      con.apply var $ mergeAliases ur.fullResult am2

        let eqs = mkEqualsTuple $ zip (pushIn a1 %search) (pushIn a2 %search)
        let sig =
          flip piAll a1 $
            flip piAll a2 $ `((~(lhsCon) ~=~ ~(rhsCon)) -> ~(eqs))
        let lhs = mkDoubleBinds (cast $ zip a1 a2) (var n) .$ `(Refl)
        pure
          [ public' n sig
          , def n $ singleton $ patClause lhs $ tupleOfN (length mcon.args) `(Refl)
          ]

    ||| Derive multiinjectivity for all polymorphic constructors that have
    ||| a specialised equivalent
    mkMultiInjDecls :
      UniResults -> (mt : TypeInfo) -> (0 _ : AllTyArgsNamed mt) => m $ List Decl
    mkMultiInjDecls ur specTy =
      logBounds "specialiseData.mkMultiInjDecls" [specTy] $ do
        let s = map2UConsN mkMultiInjDecl ur specTy
        join <$> sequence s

    ----------------------------------
    --- MULTICONGRUENCY DERIVATION ---
    ----------------------------------

    ||| Derive multicongruency for a specialised constructor
    |||
    ||| mCongN : forall argsN, argsN'; conN argsN === conN argsN'
    mkMultiCongDecl :
      UnificationResult ->
      (mt : TypeInfo) ->
      (0 _ : AllTyArgsNamed mt) =>
      (pCon : Con) ->
      (0 _ : ConArgsNamed pCon) =>
      (mCon : Con) ->
      (0 mn : ConArgsNamed mCon) =>
      Nat ->
      m $ List Decl
    mkMultiCongDecl ur mt _ mcon i =
      logBounds "specialiseData.mkMultiCongDecl" [mt, mcon] $ do
        let S _ = length mcon.args
        | _ => pure []
        let n = fromString "mCong\{show i}"
        let 0 _ = conArgsNamed @{mn}
        let Element ourArgs _ = makeArgsImplicit mcon.args
        (Element a1 _, am1) <- genArgAliases ourArgs
        (Element a2 _, am2) <- genArgAliases ourArgs
        let lhsCon = mcon.apply var $ mergeAliases ur.fullResult am1
        let rhsCon = mcon.apply var $ mergeAliases ur.fullResult am2
        let eqs = mkEqualsTuple $ zip (pushIn a1 %search) (pushIn a2 %search)
        let sig =
          flip piAll a1 $ flip piAll a2 $ `(~(eqs) -> (~(lhsCon) ~=~ ~(rhsCon)))
        let lhs = mkDoubleBinds (cast $ zip a1 a2) (var n) .$ tupleOfN (length mcon.args) `(Refl)
        pure
          [ public' n sig
          , def n $ singleton $ patClause lhs $ `(Refl)
          ]

    ||| Derive multicongruency for all specialised constructors
    mkMultiCongDecls :
      UniResults -> (mt : TypeInfo) -> (0 _ : AllTyArgsNamed mt) => m $ List Decl
    mkMultiCongDecls ur specTy =
      logBounds "specialiseData.mkMultiCongDecls" [specTy] $ do
        let s = map2UConsN mkMultiCongDecl ur specTy
        join <$> sequence s

  -----------------------------------
  --- CAST INJECTIVITY DERIVATION ---
  -----------------------------------

  ||| Make a clause for the cast injectivity proof
  mkCastInjClause :
    Elaboration m =>
    (tal1, tal2 : (List Arg, List (Name, Name))) ->
    (n1, n2 : Name) ->
    UnificationResult ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    (con : Con) ->
    (0 cn : ConArgsNamed con) =>
    (mcon : Con) ->
    (0 mcn : ConArgsNamed mcon) =>
    Nat ->
    m Clause
  mkCastInjClause (ta1, tam1) (ta2, tam2) n1 n2 ur mt _ con n =
    logBounds "specialiseData.mkCastInjClause" [mt, con] $ do
      let 0 _ = conArgsNamed @{mcn}
      (Element a1 _, am1) <- genArgAliases con.args
      (Element a2 _, am2) <- genArgAliases con.args
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
      pure $ bta2 .! (n1, lhsCon) .! (n2, rhsCon) .$ bindVar "r" .= patRhs

  ||| Derive cast injectivity proof
  mkCastInjDecls :
    Elaboration m =>
    UniResults ->
    (mt : TypeInfo) ->
    (0 mtp : AllTyArgsNamed mt) =>
    m $ List Decl
  mkCastInjDecls ur ti =
    logBounds "specialiseData.mkCastInjDecls" [ti] $ do
      let Element prepArgs prf = hideExplicitArgs ti.args @{mtp.tyArgsNamed}
      ta1@(Element a1 _, am1) <- genArgAliases prepArgs
      ta2@(Element a2 _, am2) <- genArgAliases prepArgs
      xVar <- genSym "x"
      yVar <- genSym "y"
      let mToPVar = var $ inGenNS t "mToP"
      let mToPImplVar = var $ inGenNS t "mToPImpl"
      let arg1 = MkArg MW ImplicitArg (Just xVar) $
                  ti.apply var $ fromList $ mapSnd var <$> am1
      let arg2 = MkArg MW ImplicitArg (Just yVar) $
                  ti.apply var $ fromList $ mapSnd var <$> am2
      let eqs =
        `((~(aliasedApp (cast am1) mToPImplVar .$ var xVar)
           ~=~
           ~(aliasedApp (cast am2) $ mToPImplVar .$ var yVar)) ->
            ~(var xVar) ~=~ ~(var yVar))
      castInjImplClauses <-
        sequence $ map2UConsN (mkCastInjClause (a1, am1) (a2, am2) xVar yVar) ur ti
      let tyArgPairs = cast $ zip ti.argNames ti.argNames
      pure
        [ public' "castInjImpl" $
            flip piAll (makeTypeArgM0 <$> a1) $
              flip piAll (makeTypeArgM0 <$> a2) $
                pi arg1 $ pi arg2 $ eqs
        , def "castInjImpl" castInjImplClauses
        , interfaceHint Public "castInj" $ forallMTArgs $
            `(Injective ~(aliasedApp tyArgPairs mToPImplVar))
        , def "castInj" $ singleton $
            aliasedAppBind tyArgPairs `(castInj) .= `(MkInjective castInjImpl)
        ]

  -------------------------------------
  --- DECIDABLE EQUALITY DERIVATION ---
  -------------------------------------

  ||| Decidable equality signatures
  mkDecEqImplSig : (mt : TypeInfo) -> (0 _ : AllTyArgsNamed mt) => TTImp
  mkDecEqImplSig ti =
    let tInv = ti.apply var empty
    in forallMTArgs $
      piAll
        `(Dec (Equal {a = ~tInv} {b = ~tInv} x1 x2))
        [ MkArg MW AutoImplicit Nothing `(DecEq ~(t.fullInvocation))
        , MkArg MW ExplicitArg (Just "x1") tInv
        , MkArg MW ExplicitArg (Just "x2") tInv
        ]

  ||| Decidable equality clause
  mkDecEqImplClause : Clause
  mkDecEqImplClause =
    let mToPImpl = var $ inGenNS t "mToPImpl"
    in `(decEqImpl x1 x2)
        .= `(decEqInj {f = ~mToPImpl} $ decEq (~mToPImpl x1) (~mToPImpl x2))


  ||| Derive decidable equality
  mkDecEqDecls :
    Elaboration m =>
    UniResults ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    m $ List Decl
  mkDecEqDecls _ ti = do
    mkDecEq <- var <$> try (getMk DecEq) (fail "Internal specialiser error: getMk failed.")
    pure $
      [ public' "decEqImpl" $ mkDecEqImplSig ti
      , def "decEqImpl" [ mkDecEqImplClause ]
      , interfaceHint Public "decEq'" $ forallMTArgs
        `(DecEq ~(t.fullInvocation) => DecEq ~(ti.apply var empty))
      , def "decEq'"
        [ `(decEq') .= `(~mkDecEq ~(var $ inGenNS t "decEqImpl")) ]
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
    [ public' "showImpl" $
      forallMTArgs
        `(Show ~(t.fullInvocation) => ~(ti.apply var empty) -> String)
    , def "showImpl" [ `(showImpl x) .= `(show $ ~mToPImpl x) ]
    , public' "showPrecImpl" $
      forallMTArgs
        `(Show ~(t.fullInvocation) => Prec -> ~(ti.apply var empty) -> String)
    , def "showPrecImpl"
      [ `(showPrecImpl p x) .= `(showPrec p $ ~mToPImpl x) ]
    , interfaceHint Public "show'" $ forallMTArgs $
      `(Show ~(t.fullInvocation) => Show ~(ti.apply var empty))
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
    let tInv = ti.apply var empty
    [ public' "eqImpl" $
      forallMTArgs
        `(Eq ~(t.fullInvocation) => ~tInv -> ~tInv -> Bool)
    , def "eqImpl" [ `(eqImpl x y) .= `((~mToPImpl x) == (~mToPImpl y)) ]
    , public' "neqImpl" $
      forallMTArgs
        `(Eq ~(t.fullInvocation) => ~tInv -> ~tInv -> Bool)
    , def "neqImpl" [ `(neqImpl x y) .= `((~mToPImpl x) /= (~mToPImpl y)) ]
    , interfaceHint Public "eq'" $ forallMTArgs $
      `(Eq ~(t.fullInvocation) => Eq ~tInv)
    , def "eq'" [ `(eq') .= `(MkEq eqImpl neqImpl) ]
    ]

  ------------------------------------
  --- POLY TO POLY CAST DERIVATION ---
  ------------------------------------

  ||| Generate specialised to polimorphic type conversion function signature
  mkPToMImplSig :
    UniResults ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    TTImp
  mkPToMImplSig _ mt =
    forallMTArgs $ arg t.fullInvocation .-> mt.apply var empty

  ||| Generate specialised to polimorphic type conversion function clause
  ||| for given constructor
  mkPToMImplClause :
    UnificationResult ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    (pCon : Con) ->
    (0 _ : ConArgsNamed pCon) =>
    (mCon : Con) ->
    (0 _ : ConArgsNamed mCon) =>
    Nat ->
    Clause
  mkPToMImplClause ur _ con mcon _ =
    var "pToMImpl" .$ con.apply bindVar
      (substituteVariables
        (fromList $ argsToBindMap $ con.args) <$> ur.fullResult)
      .= mcon.apply var ur.fullResult

  ||| Generate specialised to polimorphic type conversion function declarations
  mkPToMImplDecls :
    UniResults ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    List Decl
  mkPToMImplDecls urs mt = do
    let sig = mkPToMImplSig urs mt
    let clauses = map2UConsN mkPToMImplClause urs mt
    [ public' "pToMImpl" sig
    , def "pToMImpl" clauses
    ]

  ||| Generate specialised to polimorphic cast signature
  mkPToMSig : (mt : TypeInfo) -> (0 _ : AllTyArgsNamed mt) => TTImp
  mkPToMSig mt = do
    forallMTArgs $ `(Cast ~(t.fullInvocation) ~(mt.apply var empty))

  ||| Generate specialised to polimorphic cast declarations
  mkPToMDecls : (mt : TypeInfo) -> (0 _ : AllTyArgsNamed mt) => List Decl
  mkPToMDecls mt =
    [ interfaceHint Public "pToM" $ mkPToMSig mt
    , def "pToM" [ (var "pToM") .= `(MkCast pToMImpl)]
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
    let tInv = ti.apply var empty
    [ public' "fromStringImpl" $
        forallMTArgs
          `(FromString ~(t.fullInvocation) => String -> ~tInv)
    , def "fromStringImpl"
      [ `(fromStringImpl @{fs} s) .= `(~pToMImpl $ fromString @{fs} s) ]
    , interfaceHint Public "fromString'" $
        forallMTArgs `(FromString ~(t.fullInvocation) => FromString ~tInv)
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
    let tInv = ti.apply var empty
    [ public' "numImpl" $
        forallMTArgs
          `(Num ~(t.fullInvocation) => Integer -> ~tInv)
    , def "numImpl"
      [ `(numImpl @{fs} s) .= `(~pToMImpl $ Num.fromInteger @{fs} s) ]
    , public' "plusImpl" $
        forallMTArgs
          `(Num ~(t.fullInvocation) => ~tInv -> ~tInv -> ~tInv)
    , def "plusImpl"
        [ `(plusImpl @{fs} a b ) .= `(~pToMImpl $ (+) @{fs} (~mToPImpl a) (~mToPImpl b)) ]
    , public' "starImpl" $
        forallMTArgs
          `(Num ~(t.fullInvocation) => ~tInv -> ~tInv -> ~tInv)
    , def "starImpl"
        [ `(starImpl @{fs} a b ) .= `(~pToMImpl $ (*) @{fs} (~mToPImpl a) (~mToPImpl b)) ]
    , interfaceHint Public "num'" $
        forallMTArgs `(Num ~(t.fullInvocation) => Num ~tInv)
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
  specDecls : Elaboration m => UniResults -> (mt : TypeInfo) -> (0 _ : AllTyArgsNamed mt) => m $ List Decl
  specDecls uniResults specTy = do
    let specTyDecl = specTy.decl
    logPoint {level=DetailedTrace} "specialiseData.specDecls" [specTy]
      "specTyDecl : \{show specTyDecl}"
    let mToPImplDecls = mkMToPImplDecls uniResults specTy
    logPoint {level=DetailedTrace} "specialiseData.specDecls" [specTy]
      "mToPImplDecls : \{show mToPImplDecls}"
    let mToPDecls = mkMToPDecls specTy
    logPoint {level=DetailedTrace} "specialiseData.specDecls" [specTy]
      "mToP : \{show mToPDecls}"
    multiInjDecls <- mkMultiInjDecls uniResults specTy
    logPoint {level=DetailedTrace} "specialiseData.specDecls" [specTy]
      "multiInj : \{show multiInjDecls}"
    multiCongDecls <- mkMultiCongDecls uniResults specTy
    logPoint {level=DetailedTrace} "specialiseData.specDecls" [specTy]
      "multiCong : \{show multiCongDecls}"
    castInjDecls <- mkCastInjDecls uniResults specTy
    logPoint {level=DetailedTrace} "specialiseData.specDecls" [specTy]
      "castInj : \{show castInjDecls}"
    decEqDecls <- mkDecEqDecls uniResults specTy
    logPoint {level=DetailedTrace} "specialiseData.specDecls" [specTy]
      "decEq : \{show decEqDecls}"
    let showDecls = mkShowDecls uniResults specTy
    logPoint {level=DetailedTrace} "specialiseData.specDecls" [specTy]
      "Show : \{show showDecls}"
    let eqDecls = mkEqDecls uniResults specTy
    logPoint {level=DetailedTrace} "specialiseData.specDecls" [specTy]
      "Eq : \{show eqDecls}"
    let pToMImplDecls = mkPToMImplDecls uniResults specTy
    logPoint {level=DetailedTrace} "specialiseData.specDecls" [specTy]
      "pToMImplDecls : \{show pToMImplDecls}"
    let pToMDecls = mkPToMDecls specTy
    logPoint {level=DetailedTrace} "specialiseData.specDecls" [specTy]
      "pToM : \{show pToMDecls}"
    let fromStringDecls = mkFromStringDecls specTy
    logPoint {level=DetailedTrace} "specialiseData.specDecls" [specTy]
      "fromString : \{show fromStringDecls}"
    let numDecls = mkNumDecls specTy
    logPoint {level=DetailedTrace} "specialiseData.specDecls" [specTy]
      "num : \{show numDecls}"
    let onFull : List Decl =
      if any isUndecided uniResults
          then []
          else join
            [ pToMImplDecls
            , pToMDecls
            , fromStringDecls
            , numDecls
            ]
    pure $ singleton $ INamespace EmptyFC (MkNS [ show t.resultName ]) $
      specTyDecl :: join
        [ mToPImplDecls
        , mToPDecls
        , multiInjDecls
        , multiCongDecls
        , castInjDecls
        , decEqDecls
        , showDecls
        , eqDecls
        ] ++ onFull

-------------------------------------
--- SPECIALISATION TASK INTERFACE ---
-------------------------------------

||| Valid task lambda interface
|||
||| Auto-implemented by any Type or any function that returns Type.
export
interface TaskLambda (t : Type) where

export
TaskLambda Type

export
TaskLambda b => TaskLambda (a -> b)

export
TaskLambda b => TaskLambda (a => b)

export
TaskLambda b => TaskLambda ({_ : a} -> b)

export
TaskLambda b => TaskLambda ((0 _ : a) -> b)

export
TaskLambda b => TaskLambda ((0 _ : a) => b)

export
TaskLambda b => TaskLambda ({0 _ : a} -> b)

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
  Elaboration m =>
  (nsProvider : NamespaceProvider m) =>
  (unifier : CanUnify m) =>
  MonadError SpecialisationError m =>
  (resultName : Name) ->
  (resultKind : TTImp) ->
  (resultContent : TTImp) ->
  m (TypeInfo, List Decl)
specialiseDataRaw resultName resultKind resultContent = do
  let resultKind = mapTTImp cleanupHoleAutoImplicitsImpl $ cleanupNamedHoles resultKind
  let resultContent = mapTTImp cleanupHoleAutoImplicitsImpl $ cleanupNamedHoles resultContent
  task <- getTask resultName resultKind resultContent
  logPoint {level=DetailedTrace} "specialiseData" [task.polyTy] "Specialisation task: \{show task}"
  uniResults <- sequence $ mapCons task $ unifyCon task
  let Element specTy specTyNamed = mkSpecTy task uniResults
  decls <- specDecls task uniResults specTy
  pure (specTy, decls)

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
specialiseData :
  TaskLambda taskT =>
  Monad m =>
  Elaboration m =>
  (nsProvider : NamespaceProvider m) =>
  (unifier : CanUnify m) =>
  MonadError SpecialisationError m =>
  (resultName : Name) ->
  (0 task : taskT) ->
  m (TypeInfo, List Decl)
specialiseData resultName task = do
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
||| specialiseData'' `{VF} $ \n => Fin n
||| ```
export
specialiseData'' :
  Elaboration m =>
  (nsProvider : NamespaceProvider m) =>
  (unifier : CanUnify m) =>
  TaskLambda taskT =>
  Name ->
  (0 task: taskT) ->
  m $ List Decl
specialiseData'' resultName task = do
  Right (specTy, decls) <-
    runEitherT {m} {e=SpecialisationError} $
      specialiseData resultName task
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
||| %runElab specialiseData' `{VF} $ \n => Fin n
||| ```
export
specialiseData' :
  Elaboration m =>
  (nsProvider : NamespaceProvider m) =>
  (unifier : CanUnify m) =>
  TaskLambda taskT =>
  Name ->
  (0 task: taskT) ->
  m ()
specialiseData' resultName task =
  specialiseData'' resultName task >>= declare

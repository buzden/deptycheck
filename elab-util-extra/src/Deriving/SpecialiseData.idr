module Deriving.SpecialiseData

import public Control.Monad.Reader.Tuple
import public Data.SnocList
import public Derive.Prelude
import public Data.List1
import public Data.Vect
import public Data.List
import public Data.Either
import public Data.SortedMap
import public Data.SortedSet
import public Data.SortedMap.Dependent
import public Language.Mk
import public Language.Reflection
import public Language.Reflection.Expr
import public Language.Reflection.Syntax
import public Language.Reflection.Syntax.Ops
import public Language.Reflection.TT
import public Language.Reflection.TTImp
import public Language.Reflection.Unify
import public Language.Reflection.Util
import public Language.Reflection.VarSubst
import public Syntax.IHateParens

%language ElabReflection

----------------------------------
--- UNIFICATION TASK INTERFACE ---
----------------------------------

||| Valid type task interface
|||
||| Auto-implemented by any Type or any function that returns Type.
public export
interface TypeTask (t : Type) where

public export
TypeTask Type

public export
TypeTask b => TypeTask (a -> b)

||| Specialisation error
public export
data SpecialisationError : Type where
  ||| Failed to extract invocation from task
  InvocationExtractionError : SpecialisationError
  ||| Failed to extract polymorphic type name from task
  TaskTypeExtractionError : SpecialisationError
  ||| All constructors failed unification
  EmptyMonoConError : SpecialisationError

public export
Show SpecialisationError where
  show InvocationExtractionError = "InvocationExtractionError"
  show TaskTypeExtractionError = "TaskTypeExtractionError"
  show EmptyMonoConError = "EmptyMonoConError"

||| Extract contents of a lambda
taskInvocation :
  Monad m =>
  Elaboration m =>
  MonadError SpecialisationError m =>
  TTImp ->
  m TTImp
taskInvocation  (ILam _ _ _ _ _ r)   = taskInvocation r
taskInvocation x@(IApp _ _ _)        = pure x
taskInvocation x@(INamedApp _ _ _ _) = pure x
taskInvocation x@(IAutoApp _ _ _)    = pure x
taskInvocation x@(IWithApp _ _ _)    = pure x
taskInvocation x@(IVar _ _)          = pure x
taskInvocation x                     =
  throwError InvocationExtractionError

||| Extract a task's inner typename
taskTName :
  Monad m =>
  Elaboration m =>
  MonadError SpecialisationError m =>
  TTImp -> m Name
taskTName (IVar _ n)          = pure n
taskTName (IApp _ f _)        = taskTName f
taskTName (INamedApp _ f _ _) = taskTName f
taskTName (IAutoApp _ f _)    = taskTName f
taskTName (IWithApp _ f _)    = taskTName f
taskTName t                   =
  throwError TaskTypeExtractionError

-------------------------
--- CUSTOM DATA TYPES ---
-------------------------

||| Specialisation task
record MonoTask where
  constructor MkMonoTask
  ||| Full unification task
  taskQuote      : TTImp
  ||| Unification task type
  taskType       : TTImp
  ||| Namespace in which monomorphise was called
  ns             : Namespace
  ||| Name of polymorphic type
  typeName       : Name
  ||| Name of monomorphic type
  outputName     : Name
  ||| Invocation of polymorphic type extracted from unification task
  fullInvocation : TTImp
  ||| Polymorphic type's TypeInfo
  polyTy         : TypeInfo

public export
Show MonoTask where
  show (MkMonoTask tq tt ns tn on fi pt) = "MkMonoTask \{show tq} \{show tt} \{show ns} \{show tn} \{show on} \{show fi} <typeinfo>"

||| Polymorphic type's constructor
(.Con) : MonoTask -> Type
(.Con) task = Con task.polyTy.arty task.polyTy.args

namespace TypeInfo
  ||| Type's constructor
  public export
  (.Con) : TypeInfo -> Type
  (.Con) t = Con t.arty t.args

||| Unification result
record UnificationResult where
  constructor MkUR
  ||| Task given to the unifier
  task : UnificationTask
  ||| Dependency graph returned by the unifier
  dg : DependencyGraph
  ||| LHS free variable (polymorphic constructor argument) values
  lhsResult : SortedMap Name TTImp
  ||| RHS free variable (monomorphic type argument) values
  rhsResult : SortedMap Name TTImp
  ||| All free variable values
  fullResult : SortedMap Name TTImp
  ||| Order of dependency of free variables without values
  ||| (monomorphic constructor arguments)
  order : List $ Fin dg.freeVars

%runElab derive "UnificationResult" [Show]

||| Unification results for the whole type
UniResults : Type
UniResults = List $ Either String UnificationResult

------------------------------
--- NAMESPACE MANIPULATION ---
------------------------------

||| Get namespace in which elaborator script is executed
getNS : Elaboration m => m Namespace
getNS = do
  NS nsn _ <- inCurrentNS ""
  | _ => fail "inCurrentNS failed?"
  pure nsn

||| Prepend namespace into which everything is generated to name
inGenNS : MonoTask -> Name -> Name
inGenNS task (NS (MkNS subs) n) = do
  let MkNS tns = task.ns
  NS (MkNS $ subs ++ show task.outputName :: tns) $ dropNS n
inGenNS task n = do
  let MkNS tns = task.ns
  NS (MkNS $ show task.outputName :: tns) $ dropNS n

---------------------
--- TASK ANALYSIS ---
---------------------

||| Run `cleanupNamedHoles` over a `PiInfo`'s inner `TTImp`
cleanupPiInfo : PiInfo TTImp -> PiInfo TTImp
cleanupPiInfo (DefImplicit t) = DefImplicit $ cleanupNamedHoles t
cleanupPiInfo p = p

||| Run `cleanupNamedHoles` over all `Arg`'s `TTImp`s
cleanupArg : Arg -> Arg
cleanupArg = { type $= cleanupNamedHoles, piInfo $= cleanupPiInfo }

||| Convert MissingInfo for compatibility with `cleanupNamedHoles`
cleanupMissing : MissingInfo p -> MissingInfo (cleanupPiInfo p)
cleanupMissing Auto = Auto
cleanupMissing Implicit = Implicit
cleanupMissing Deflt = Deflt

||| Run `cleanupNamedHoles` over all `AppArg`'s `TTImp`s
cleanupAppArg : AppArg a -> AppArg (cleanupArg a)
cleanupAppArg (NamedApp n s) = NamedApp n $ cleanupNamedHoles s
cleanupAppArg (AutoApp s) = AutoApp $ cleanupNamedHoles s
cleanupAppArg (Regular s) = Regular $ cleanupNamedHoles s
cleanupAppArg (Missing x) = Missing $ cleanupMissing x

||| Run `cleanupNamedHoles` over all `AppArgs`'s `TTImp`s
cleanupAppArgs : {0 n : Nat} -> {0 a : Vect n Arg} -> AppArgs a -> AppArgs (map SpecialiseData.cleanupArg a)
cleanupAppArgs [] = []
cleanupAppArgs (x :: xs) = cleanupAppArg x :: cleanupAppArgs xs

||| Run `cleanupNamedHoled` over all `Con`'s `TTImp`s
cleanupCon : Con a b -> Con a (map SpecialiseData.cleanupArg b)
cleanupCon = { args $= map cleanupArg, typeArgs $= cleanupAppArgs }

||| Run `cleanupNamedHoles` over all `TypeInfo`'s `TTImp`s
cleanupTypeInfo : TypeInfo -> TypeInfo
cleanupTypeInfo (MkTypeInfo name arty args argNames cons) =
  MkTypeInfo name arty (cleanupArg <$> args) argNames (cleanupCon <$> cons)

||| Get all the information needed for monomorphisation from task
getTask :
  TypeTask l =>
  Monad m =>
  Elaboration m =>
  MonadError SpecialisationError m =>
  l ->
  Name ->
  m MonoTask
getTask l' outputName = with Prelude.(>>=) do
  taskQuote : TTImp <- cleanupNamedHoles <$> quote l'
  taskType : TTImp <- cleanupNamedHoles <$> quote l
  ns <- getNS
  fullInvocation <- taskInvocation taskQuote
  typeName : Name <- taskTName fullInvocation
  polyTy <- cleanupTypeInfo <$> Types.getInfo' typeName
  pure $ MkMonoTask
    { taskQuote
    , taskType
    , ns
    , typeName
    , outputName
    , fullInvocation
    , polyTy
    }


---------------------------
--- Constructor Mapping ---
---------------------------

||| Run monadic operation on all constructors of monomorphic type
mapCons :
  Monad m =>
  (f : (t : MonoTask) -> t.Con -> m r) ->
  MonoTask ->
  m $ List r
mapCons f task = traverse (f task) task.polyTy.cons

||| Run monadic operation on all constructors for which unification succeeded
mapUCons :
  Monad m =>
  (f : (t : MonoTask) -> UnificationResult -> t.Con -> m r) ->
  MonoTask ->
  UniResults ->
  m $ List r
mapUCons f t rs = traverseA (f t) $ zip t.polyTy.cons rs
  where
    traverseA :
      (UnificationResult -> t.Con -> m r) ->
      List (t.Con, Either String UnificationResult) ->
      m (List r)
    traverseA f [] = pure []
    traverseA f ((con, Left _) :: xs) = traverseA f xs
    traverseA f ((con, Right res) :: xs) = [| f res con :: traverseA f xs |]

||| Map over all constructors for which unification succeeded
mapUCons' :
  (f : (t : MonoTask) -> UnificationResult -> t.Con -> r) ->
  MonoTask ->
  UniResults ->
  List r
mapUCons' f t rs = runIdentity $ mapUCons (\a,b,c => Id $ f a b c) t rs

||| Run monadic operation on all pairs of monomorphic and polymorphic constructors
map2UCons :
  Monad m =>
  (f : (t : MonoTask) -> UnificationResult -> (mt: TypeInfo) -> t.Con -> mt.Con -> m r) ->
  MonoTask ->
  UniResults ->
  TypeInfo ->
  m $ List r
map2UCons f t rs mt = traverseA $ zip t.polyTy.cons (zip mt.cons rs)
  where
    traverseA :
      List (t.Con, mt.Con, Either String UnificationResult) ->
      m (List r)
    traverseA [] = pure []
    traverseA ((con, (mcon, Left _)) :: xs) = traverseA xs
    traverseA ((con, (mcon, Right res)) :: xs) = [| f t res mt con mcon :: traverseA xs |]

||| Map over all pairs of monomorphic and polymorphic constructors
map2UCons' :
  (f : (t : MonoTask) -> UnificationResult -> (mt: TypeInfo) -> t.Con -> mt.Con -> r) ->
  MonoTask ->
  UniResults ->
  TypeInfo ->
  List r
map2UCons' f t rs mt =
  runIdentity $ map2UCons (\a,b,c,d,e => Id $ f a b c d e) t rs mt

||| Run monadic operation on all pairs of monomorphic and polymorphic constructors
map2UConsN :
  Monad m =>
  (f : (t : MonoTask) -> UnificationResult -> (mt: TypeInfo) -> t.Con -> mt.Con -> Nat -> m r) ->
  MonoTask ->
  UniResults ->
  TypeInfo ->
  m $ List r
map2UConsN f t rs mt = traverseA 0 $ zip t.polyTy.cons (zip mt.cons rs)
  where
    traverseA :
      Nat ->
      List (t.Con, mt.Con, Either String UnificationResult) ->
      m (List r)
    traverseA n [] = pure []
    traverseA n ((con, (mcon, Left _)) :: xs) = traverseA (S n) xs
    traverseA n ((con, (mcon, Right res)) :: xs) =
      [| f t res mt con mcon n :: traverseA (S n)  xs|]

||| Map over all pairs of monomorphic and polymorphic constructors
map2UConsN' :
  (f : (t : MonoTask) -> UnificationResult -> (mt: TypeInfo) -> t.Con -> mt.Con -> Nat -> r) ->
  MonoTask ->
  UniResults ->
  TypeInfo ->
  List r
map2UConsN' f t rs mt =
  runIdentity $ map2UConsN (\a,b,c,d,e,g => Id $ f a b c d e g) t rs mt

-------------------------------
--- Constructor unification ---
-------------------------------

||| Apply all arguments as specified in AppArgs to TTImp
appArgs : TTImp -> AppArgs a -> TTImp
appArgs t (x :: xs) = appArgs (appArg t x) xs
appArgs t []        = t

||| Find all variables which have no value
filterEmpty : Vect _ FVData -> List (Name, TTImp)
filterEmpty = foldl myfun []
  where
    myfun : List (Name, TTImp) -> FVData -> List (Name, TTImp)
    myfun xs x =
      case x.value of
        Just val => (x.name, val) :: xs
        Nothing => xs

||| Run unification for a given polymorphic constructor
unifyCon : Elaboration m => (t : MonoTask) -> t.Con -> EitherT String m UnificationResult
unifyCon t con = do
  let conRet = appArgs .| var t.typeName .| con.typeArgs
  let (argsR, tRet) = unLambda t.taskQuote
  argsR <- traverse .| tryFromArg "nameless arg!" .| fromList argsR
  argsL <- traverse .| tryFromArg "nameless arg!" .| con.args
  let uniTask = MkUniTask _ argsL conRet _ argsR tRet
  logMsg "SpecialiseData" 0 "Unifier task: \{show uniTask}"
  Right uniRes <- tryError $ unifyWithCompiler uniTask
  | Left err => MkEitherT $ do
    logMsg "SpecialiseData" 0 "Unifier failed: \{err}"
    pure $ Left err
  logMsg "SpecialiseData" 0 "Unifier returned: \{show uniRes}"
  let fvOrder = flattenEmpties uniRes
  logMsg "SpecialiseData" 0 "Arguments: \{show fvOrder}"
  let urList = filterEmpty uniRes.fvData
  logMsg "SpecialiseData" 0 "FullResult: \{show urList}"
  let (lhsRL, rhsRL) = List.splitAt con.arty urList
  MkEitherT $ pure $ Right $
    MkUR
      { task = uniTask
      , dg = uniRes
      , lhsResult = fromList lhsRL
      , rhsResult = fromList rhsRL
      , fullResult = fromList urList
      , order = toList fvOrder
      }

-------------------------------
--- TypeInfo/Con EXTENSIONS ---
-------------------------------

||| Given a type name to which constructor belongs, calculate its signature
conSig : Con _ _ -> TTImp -> TTImp
conSig con ty = piAll .| appArgs ty con.typeArgs .| toList con.args

||| Given a type name to which constructor belongs, calculate its ITy
conITy : TTImp -> Con _ ags -> ITy
conITy retTy con = mkTy .| dropNS con.name .| conSig con retTy

||| Generate a declaration from TypeInfo
(.decl) : TypeInfo -> Decl
(.decl) ti =
  iData Public ti.name tySig [] conITys
  where
    tySig = piAll type $ toList ti.args
    conITys = toList $ conITy (var ti.name) <$> ti.cons

||| Generate AppArg for given Arg, substituting names for values if present
(.appArg) : (arg : Arg) -> SortedMap Name TTImp -> Maybe $ AppArg arg
(.appArg) (MkArg count piInfo (Just n) type) argVals = do
  let val = fromMaybe (var n) $ lookup n argVals
  Just $ case piInfo of
    ExplicitArg => Regular val
    AutoImplicit => AutoApp val
    _ => NamedApp n val
(.appArg) (MkArg count piInfo Nothing type) argVals = Nothing

||| Generate AppArg for given Arg, substituting names for values if present
||| and binding otherwise
(.appArgBind) : (arg : Arg) -> SortedMap Name TTImp -> Maybe $ AppArg arg
(.appArgBind) (MkArg count piInfo (Just n) type) argVals = do
  let val = fromMaybe (bindVar n) $ lookup n argVals
  Just $ case piInfo of
    ExplicitArg => Regular val
    AutoImplicit => AutoApp val
    _ => NamedApp n val
(.appArgBind) (MkArg count piInfo Nothing type) argVals = Nothing

||| Generate AppArg for given Arg, substituting names for values if present
||| and using hole otherwise
(.appArgHole) : (arg : Arg) -> SortedMap Name TTImp -> Maybe $ AppArg arg
(.appArgHole) (MkArg count piInfo (Just n) type) argVals = do
  let val = fromMaybe (Implicit EmptyFC False) $ lookup n argVals
  Just $ case piInfo of
    ExplicitArg => Regular val
    AutoImplicit => AutoApp val
    _ => NamedApp n val
(.appArgHole) (MkArg count piInfo Nothing type) argVals = Nothing

||| Generate AppArgs for given argument vector, substituting names for values if present
(.appArgs) : (args: Vect _ Arg) -> SortedMap Name TTImp -> Maybe $ AppArgs args
(.appArgs) [] argVals = Just []
(.appArgs) (x :: xs) argVals = [| x.appArg argVals :: xs.appArgs argVals |]

||| Generate AppArgs for given argument vector, substituting names for values if present
||| and binding otherwise
(.appArgsBind) :
  (args: Vect _ Arg) ->
  SortedMap Name TTImp ->
  Maybe $ AppArgs args
(.appArgsBind) [] argVals = Just []
(.appArgsBind) (x :: xs) argVals =
  [| x.appArgBind argVals :: xs.appArgsBind argVals |]

||| Generate AppArgs for given argument vector, substituting names for values if present
||| and using hole otherwise
(.appArgsHole) :
  (args: Vect _ Arg) ->
  SortedMap Name TTImp ->
  Maybe $ AppArgs args
(.appArgsHole) [] argVals = Just []
(.appArgsHole) (x :: xs) argVals =
  [| x.appArgHole argVals :: xs.appArgsHole argVals |]


namespace TypeInfoInvoke
  ||| Generate type invocation, substituting argument values
  public export
  (.invoke) : TypeInfo -> SortedMap Name TTImp -> TTImp
  (.invoke) t vals =
    fromMaybe `(_) $ appArgs (var t.name) <$> t.args.appArgs vals

  ||| Generate binding type invocation, substituting argument values
  public export
  (.invokeBind) : TypeInfo -> SortedMap Name TTImp -> TTImp
  (.invokeBind) t vals =
    fromMaybe `(_) $ appArgs (var t.name) <$> t.args.appArgsBind vals

namespace ConInvoke
  ||| Generate constructor invocation, substituting argument values
  public export
  (.invoke) : Con _ _ -> SortedMap Name TTImp -> TTImp
  (.invoke) con vals =
    fromMaybe `(_) $ appArgs (var con.name) <$> con.args.appArgs vals

  ||| Generate binding constructor invocation, substituting argument values
  public export
  (.invokeBind) : Con _ _ -> SortedMap Name TTImp -> TTImp
  (.invokeBind) con vals =
    fromMaybe `(_) $ appArgs (var con.name) <$> con.args.appArgsBind vals

  public export
  (.invokeHole) : Con _ _ -> SortedMap Name TTImp -> TTImp
  (.invokeHole) con vals =
    fromMaybe `(_) $ appArgs (var con.name) <$> con.args.appArgsHole vals
-----------------------------------
--- MONOMORPHIC TYPE GENERATION ---
-----------------------------------

||| Generate argument of a monomorphic constructor
mkMonoArg :
  (t : MonoTask) ->
  (ur : UnificationResult) ->
  Fin (ur.dg.freeVars) ->
  Arg
mkMonoArg t ur fvId = do
  let fvData = index fvId ur.dg.fvData
  MkArg fvData.rig fvData.piInfo (Just fvData.name) fvData.type

||| Generate a monomorphic constructor
mkMonoCon :
  (newArgs : _) ->
  (t : MonoTask) ->
  UnificationResult ->
  t.Con ->
  Con _ newArgs
mkMonoCon newArgs t ur pCon = do
  let args = mkMonoArg t ur <$> Vect.fromList ur.order
  let Just typeArgs = newArgs.appArgs ur.fullResult
  | _ => ?mmc_rhs
  MkCon
    { name = inGenNS t $ dropNS pCon.name
    , arty = _
    , args
    , typeArgs
    }

||| Generate a monomorphic type
mkMonoTy : MonoTask -> UniResults -> TypeInfo
mkMonoTy t ur =
  MkTypeInfo
    { name = inGenNS t t.outputName
    , arty = _
    , args
    , argNames = map (fromMaybe (UN Underscore) . name) args
    , cons = mapUCons' (mkMonoCon args) t ur
    }
  where
    args = Vect.fromList $ fst $ unPi t.taskType

------------------------------------
--- MONO TO POLY CAST DERIVATION ---
------------------------------------

||| Substitute IPis' return type and set all arguments to implicit
rewireIPiImplicit : TTImp -> TTImp -> TTImp
rewireIPiImplicit (IPi fc count _ mn arg ret) y =
  IPi fc count ImplicitArg mn arg $ rewireIPiImplicit ret y
rewireIPiImplicit x y = y

||| Generate IPi with implicit type arguments and given return
forallMTArgs : MonoTask -> TTImp -> TTImp
forallMTArgs task = rewireIPiImplicit task.taskType

||| Generate monomorphic to polimorphic type conversion function signature
mkMToPImplSig : MonoTask -> UniResults -> TypeInfo -> TTImp
mkMToPImplSig t urs mt =
  forallMTArgs t $ arg (mt.invoke empty) .-> t.fullInvocation

argsToBindMap : List Arg -> List (Name, TTImp)
argsToBindMap [] = []
argsToBindMap (x :: xs) =
  case x.name of
    Just n => (n, bindVar n) :: argsToBindMap xs
    Nothing => argsToBindMap xs

||| Generate monomorphic to polimorphic type conversion function clause
||| for given constructor
mkMToPImplClause :
  (t : MonoTask) ->
  UnificationResult ->
  (mt : TypeInfo) ->
  t.Con ->
  mt.Con ->
  Clause
mkMToPImplClause t ur mt con mcon =
  patClause
    (var "mToPImpl" .$ mcon.invokeBind (substituteVariables (fromList $ argsToBindMap $ toList mcon.args) <$> ur.fullResult))
    (con.invoke ur.fullResult)

||| Generate monomorphic to polimorphic type conversion function declarations
mkMToPImplDecls :
  MonoTask ->
  UniResults ->
  TypeInfo ->
  List Decl
mkMToPImplDecls t urs mt = do
  let sig = mkMToPImplSig t urs mt
  let clauses = map2UCons' mkMToPImplClause t urs mt
  [ public' "mToPImpl" sig
  , def "mToPImpl" clauses
  ]

||| Generate monomorphic to polimorphic cast signature
mkMToPSig : MonoTask -> TypeInfo -> TTImp
mkMToPSig t mt = do
  forallMTArgs t $ `(Cast ~(mt.invoke empty) ~(t.fullInvocation))

||| Generate monomorphic to polimorphic cast declarations
mkMToPDecls : MonoTask -> TypeInfo -> List Decl
mkMToPDecls t mt =
  [ interfaceHint Public "mToP" $ mkMToPSig t mt
  , def "mToP" [ patClause (var "mToP") `(MkCast mToPImpl)]
  ]

-----------------------------------
--- MULTIINJECTIVITY DERIVATION ---
-----------------------------------
||| Wrap an expression in let expressions as defined by list
wrapInLets : List (Name, TTImp) -> TTImp -> TTImp
wrapInLets [] t = t
wrapInLets ((n, t') :: xs) t = iLet MW n `(_) t' $ wrapInLets xs t

||| Given a list of arguments, generate a list of aliased arguments
||| and a list of aliases
genArgAliases : Elaboration m => List Arg -> List (Name, Name) -> m (List Arg, List (Name, Name))
genArgAliases [] lnn = pure ([], lnn)
genArgAliases ((MkArg count piInfo Nothing type) :: xs) lnn =
  genArgAliases xs lnn
genArgAliases ((MkArg count piInfo (Just name) type) :: xs) lnn = do
  alias <- genSym $ show name
  (as, am) <- genArgAliases xs ((name, alias) :: lnn)
  let type = substituteVariables (fromList $ mapSnd var <$> lnn) type
  pure ((MkArg count piInfo (Just alias) type) :: as, am)

||| Given a list of aliased argument pairs, generate a list of equality type
||| for each pair
mkEqs : List (Arg, Arg) -> TTImp
mkEqs [] = `(MkUnit)
mkEqs [(a1, a2)] =
  case (a1.name, a2.name) of
    (Just a1n, Just a2n) => `(~(var a1n) ~=~ ~(var a2n))
    _ => `(MkUnit)
mkEqs ((a1, a2) :: as) =
  case (a1.name, a2.name) of
    (Just a1n, Just a2n) => `(Pair (~(var a1n) ~=~ ~(var a2n)) ~(mkEqs as))
    _ => mkEqs as

||| Given a list of aliased argument pairs [(a, b), ...], generate a series of
||| named applications: (... {a=a} {b=a})
mkDoubleBinds : SnocList (Arg, Arg) -> TTImp -> TTImp
mkDoubleBinds [<] t = t
mkDoubleBinds (as :< (a1, a2)) t =
  case (a1.name, a2.name) of
    (Just a1n, Just a2n) => mkDoubleBinds as t .! (a1n, bindVar a1n) .! (a2n, bindVar a1n)
    _ => mkDoubleBinds as t

||| Make an argument omega implicit
prepareArg : Arg -> Arg
prepareArg = { piInfo := ImplicitArg, count := MW }

||| A tuple value of multiple repeating expressons
tupleOfN : Nat -> TTImp -> TTImp
tupleOfN 0 _ = `(Unit)
tupleOfN 1 t = t
tupleOfN (S n) t = `(MkPair ~(t) ~(tupleOfN n t))

||| Map all unmapped variables from the list to their aliases
mergeAliases : SortedMap Name TTImp -> List (Name, Name) -> SortedMap Name TTImp
mergeAliases m = mergeWith (curry fst) m . fromList . map (mapSnd var)

||| Map all unmapped variables from the list to their aliases (with binding)
mergeAliasesBind : SortedMap Name TTImp -> List (Name, Name) -> SortedMap Name TTImp
mergeAliasesBind m = mergeWith (curry fst) m . fromList . map (mapSnd bindVar)

||| Derive multiinjectivity for a polymorphic constructor that has a
||| monomorphic equivalent
mkMultiInjDecl :
  Elaboration m =>
  UnificationResult ->
  Con aty ags ->
  Con aty' ags' ->
  Name ->
  m $ List Decl
mkMultiInjDecl ur con con' n = do
  let ourArgs = prepareArg <$> toList con'.args
  let (S _) = con'.arty
  | _ => pure []
  (a1, am1) <- genArgAliases ourArgs []
  (a2, am2) <- genArgAliases ourArgs []
  let lhsCon = substituteVariables (fromList $ mapSnd var <$> am1) $ con.invoke $ mergeAliases ur.fullResult am1
  let rhsCon = substituteVariables (fromList $ mapSnd var <$> am2) $ con.invoke $ mergeAliases ur.fullResult am2

  let eqs = mkEqs $ zip a1 a2
  let sig =
    flip piAll a1 $ flip piAll a2 $ `((~(lhsCon) ~=~ ~(rhsCon)) -> ~(eqs))
  let lhs = mkDoubleBinds (cast $ zip a1 a2) (var n) .$ `(Refl)
  pure
    [ public' n sig
    , def n $ singleton $ patClause lhs $ tupleOfN con'.arty `(Refl)
    ]

||| Derive multiinjectivity for all polymorphic constructors that have
||| a monomorphic equivalent
mkMultiInjDecls : Elaboration m => MonoTask -> UniResults -> TypeInfo -> m $ List Decl
mkMultiInjDecls t ur monoTy = do
  join <$>
    map2UConsN
      (\_,ur,_,tc,mc,i => mkMultiInjDecl ur tc mc $ fromString "mInj\{show i}")
      t ur monoTy

----------------------------------
--- MULTICONGRUENCY DERIVATION ---
----------------------------------

||| Derive multicongruency for a polymorphic constructor that has a
||| monomorphic equivalent
mkMultiCongDecl : Elaboration m => UnificationResult -> Con aty ags -> Name -> m $ List Decl
mkMultiCongDecl ur con n = do
  let ourArgs = prepareArg <$> toList con.args
  let (S _) = con.arty
  | _ => pure []
  (a1, am1) <- genArgAliases ourArgs []
  (a2, am2) <- genArgAliases ourArgs []
  let lhsCon = con.invoke $ mergeAliases ur.fullResult am1
  let rhsCon = con.invoke $ mergeAliases ur.fullResult am2
  let eqs = mkEqs $ zip a1 a2
  let sig =
    flip piAll a1 $ flip piAll a2 $ `(~(eqs) -> (~(lhsCon) ~=~ ~(rhsCon)))
  let lhs = mkDoubleBinds (cast $ zip a1 a2) (var n) .$ tupleOfN con.arty `(Refl)
  pure
    [ public' n sig
    , def n $ singleton $ patClause lhs $ `(Refl)
    ]

||| Derive multicongruency for all polymorphic constructors that have
||| a monomorphic equivalent
mkMultiCongDecls : Elaboration m => MonoTask -> UniResults -> TypeInfo -> m $ List Decl
mkMultiCongDecls t ur monoTy = do
  join <$>
    map2UConsN
      (\_,ur,_,_,tc,i => mkMultiCongDecl ur tc $ fromString "mCong\{show i}")
      t ur monoTy

-----------------------------------
--- CAST INJECTIVITY DERIVATION ---
-----------------------------------
||| Create a binding application of aliased arguments
bindTyArgs : SnocList (Name, Name) -> SortedMap Name TTImp -> TTImp -> TTImp
bindTyArgs [<] nm t = t
bindTyArgs (xs :< (n, an)) nm t =
  bindTyArgs xs nm t .! (an, fromMaybe (bindVar n) $ lookup n nm)

||| Create a non-binding application of aliased arguments
withTyArgs : SnocList (Name, Name) -> TTImp -> TTImp
withTyArgs [<] t = t
withTyArgs (xs :< (n, an)) t =
  withTyArgs xs t .! (n, var an)

||| Make a clause for the cast injectivity proof
mkCastInjClause :
  Elaboration m =>
  (tal1, tal2 : (List Arg, List (Name, Name))) ->
  (n1, n2 : Name) ->
  UnificationResult ->
  Con aa bb ->
  Nat ->
  m Clause
mkCastInjClause (ta1, tam1) (ta2, tam2) n1 n2 ur con n = do
  (a1, am1) <- genArgAliases (toList $ con.args) []
  (a2, am2) <- genArgAliases (toList $ con.args) []
  let am1' = fromList $ mapSnd bindVar <$> am1
  let am2' = fromList $ mapSnd bindVar <$> am2
  let ures1 = substituteVariables am1' <$> ur.fullResult
  let ures2 = substituteVariables am2' <$> ur.fullResult
  let bta1 = bindTyArgs (cast tam1) ures1 `(castInjImpl)
  let bta2 = bindTyArgs (cast tam2) ures2 bta1
  let lhsCon = con.invokeBind $ am1'
  let rhsCon = con.invokeBind $ am2'
  pure $ patClause
    (
      bta2
      .! (n1, lhsCon)
      .! (n2, rhsCon)
      .$ bindVar "r")
    (case (length a1) of
      0 => `(Refl)
      _ =>
        `(~(var $ fromString $ "mCong\{show n}")
          (~(var $ fromString $ "mInj\{show n}") r)))


||| Derive cast injectivity proof
mkCastInjDecls : Elaboration m => MonoTask -> UniResults -> TypeInfo -> m $ List Decl
mkCastInjDecls mt ur ti = do
  let prepArgs = prepareArg <$> toList ti.args
  ta1@(a1, am1) <- genArgAliases prepArgs []
  ta2@(a2, am2) <- genArgAliases prepArgs []
  xVar <- genSym "x"
  yVar <- genSym "y"
  let mToPVar = var $ inGenNS mt "mToP"
  let mToPImplVar = var $ inGenNS mt "mToPImpl"
  let arg1 = MkArg MW ImplicitArg (Just xVar) $
              ti.invoke $ fromList $ mapSnd var <$> am1
  let arg2 = MkArg MW ImplicitArg (Just yVar) $
              ti.invoke $ fromList $ mapSnd var <$> am2
  let eqs =
    `(
      ( ~(withTyArgs (cast am1) $ mToPImplVar)
        ~(var xVar) ~=~
        ~(withTyArgs (cast am2) $ mToPImplVar)
        ~(var yVar)) ->
      ~(var xVar) ~=~ ~(var yVar))
  castInjImplClauses <-
    map2UConsN (\_,ur,_,_ => mkCastInjClause ta1 ta2 xVar yVar ur) mt ur ti
  -- let mToPVar = var $ inGenNS mt "mToP"
  let tyArgPairs = cast $ toList $ zip ti.argNames ti.argNames
  pure
    [ public' "castInjImpl" $
        flip piAll a1 $ flip piAll a2 $ pi arg1 $ pi arg2 $ eqs
    , def "castInjImpl" castInjImplClauses
    , interfaceHint Public "castInj" $ forallMTArgs mt $
        `(Injective ~(withTyArgs tyArgPairs mToPImplVar))
    , def "castInj" $ singleton $
        patClause
          (bindTyArgs tyArgPairs empty `(castInj))
          `(MkInjective castInjImpl)
    ]

-------------------------------------
--- DECIDABLE EQUALITY DERIVATION ---
-------------------------------------

||| Decidable equality signatures
mkDecEqImplSig : MonoTask -> TypeInfo -> TTImp
mkDecEqImplSig mt ti =
  let tInv = ti.invoke empty
  in forallMTArgs mt $
    piAll
      `(Dec (Equal {a = ~tInv} {b = ~tInv} x1 x2))
      [ MkArg MW AutoImplicit Nothing `(DecEq ~(mt.fullInvocation))
      , MkArg MW ExplicitArg (Just "x1") tInv
      , MkArg MW ExplicitArg (Just "x2") tInv
      ]

||| Decidable equality clause
mkDecEqImplClause : MonoTask -> Clause
mkDecEqImplClause mt =
  let mToPImpl = var $ inGenNS mt "mToPImpl"
  in patClause
      `(decEqImpl x1 x2)
      `(decEqInj {f = ~mToPImpl} $ decEq (~mToPImpl x1) (~mToPImpl x2))


||| Derive decidable equality
mkDecEqDecls : Elaboration m => MonoTask -> UniResults -> TypeInfo -> m $ List Decl
mkDecEqDecls mt ur ti = do
  pure
    [ public' "decEqImpl" $ mkDecEqImplSig mt ti
    , def "decEqImpl" [ mkDecEqImplClause mt ]
    , interfaceHint Public "decEq'" $ forallMTArgs mt
      `(DecEq ~(mt.fullInvocation) => DecEq ~(ti.invoke empty))
    , def "decEq'"
      [ patClause `(decEq') `((Mk DecEq) ~(var $ inGenNS mt "decEqImpl")) ]
    ]

-----------------------
--- SHOW DERIVATION ---
-----------------------

||| Derive Show implementation via cast
mkShowDecls : MonoTask -> UniResults -> TypeInfo -> List Decl
mkShowDecls mt ur ti = do
  let mToPImpl = var $ inGenNS mt "mToPImpl"
  [ public' "showImpl" $
    forallMTArgs mt
      `(Show ~(mt.fullInvocation) => ~(ti.invoke empty) -> String)
  , def "showImpl" [ patClause `(showImpl x) `(show $ ~mToPImpl x) ]
  , public' "showPrecImpl" $
    forallMTArgs mt
      `(Show ~(mt.fullInvocation) => Prec -> ~(ti.invoke empty) -> String)
  , def "showPrecImpl"
    [ patClause `(showPrecImpl p x) `(showPrec p $ ~mToPImpl x) ]
  , interfaceHint Public "show'" $ forallMTArgs mt $
    `(Show ~(mt.fullInvocation) => Show ~(ti.invoke empty))
  , def "show'" [ patClause `(show') `(MkShow showImpl showPrecImpl) ]
  ]

---------------------
--- EQ DERIVATION ---
---------------------

||| Derive Eq implementation via cast
mkEqDecls : MonoTask -> UniResults -> TypeInfo -> List Decl
mkEqDecls mt ur ti = do
  let mToPImpl = var $ inGenNS mt "mToPImpl"
  let tInv = ti.invoke empty
  [ public' "eqImpl" $
    forallMTArgs mt
      `(Eq ~(mt.fullInvocation) => ~tInv -> ~tInv -> Bool)
  , def "eqImpl" [ patClause `(eqImpl x y) `((~mToPImpl x) == (~mToPImpl y)) ]
  , public' "neqImpl" $
    forallMTArgs mt
      `(Eq ~(mt.fullInvocation) => ~tInv -> ~tInv -> Bool)
  , def "neqImpl" [ patClause `(neqImpl x y) `((~mToPImpl x) /= (~mToPImpl y)) ]
  , interfaceHint Public "eq'" $ forallMTArgs mt $
    `(Eq ~(mt.fullInvocation) => Eq ~tInv)
  , def "eq'" [ patClause `(eq') `(MkEq eqImpl neqImpl) ]
  ]

------------------------------------
--- POLY TO MONO CAST DERIVATION ---
------------------------------------

||| Generate monomorphic to polimorphic type conversion function signature
mkPToMImplSig : MonoTask -> UniResults -> TypeInfo -> TTImp
mkPToMImplSig t urs mt =
  forallMTArgs t $ arg t.fullInvocation .-> mt.invoke empty

||| Generate monomorphic to polimorphic type conversion function clause
||| for given constructor
mkPToMImplClause :
  (t : MonoTask) ->
  UnificationResult ->
  (mt : TypeInfo) ->
  t.Con ->
  mt.Con ->
  Clause
mkPToMImplClause t ur mt con mcon =
  patClause
    (var "pToMImpl" .$ con.invokeBind
      (substituteVariables
        (fromList $ argsToBindMap $ toList con.args) <$> ur.fullResult))
    (mcon.invoke ur.fullResult)

||| Generate monomorphic to polimorphic type conversion function declarations
mkPToMImplDecls :
  MonoTask ->
  UniResults ->
  TypeInfo ->
  List Decl
mkPToMImplDecls t urs mt = do
  let sig = mkPToMImplSig t urs mt
  let clauses = map2UCons' mkPToMImplClause t urs mt
  [ public' "pToMImpl" sig
  , def "pToMImpl" clauses
  ]

||| Generate monomorphic to polimorphic cast signature
mkPToMSig : MonoTask -> TypeInfo -> TTImp
mkPToMSig t mt = do
  forallMTArgs t $ `(Cast ~(t.fullInvocation) ~(mt.invoke empty))

||| Generate monomorphic to polimorphic cast declarations
mkPToMDecls : MonoTask -> TypeInfo -> List Decl
mkPToMDecls t mt =
  [ interfaceHint Public "pToM" $ mkPToMSig t mt
  , def "pToM" [ patClause (var "pToM") `(MkCast pToMImpl)]
  ]

||| Alias all monomorphic type's arguments to rule out the possibility
||| of lhs-rhs name collision during unification (and derivation)
prepTask : Elaboration m => MonoTask -> m MonoTask
prepTask task = do
  let (lamArgs, lamRet) = unLambda task.taskQuote
  let (tyArgs, tyRet) = unPi task.taskType
  (newArgs, am) <- genArgAliases lamArgs []
  let wil = substituteVariables (fromList $ mapSnd var <$> am)
  let newTQ = foldr lam (wil lamRet) newArgs
  let newTT = piAll (wil tyRet) newArgs
  let newFI = wil task.fullInvocation
  pure $ { taskQuote := newTQ, taskType := newTT, fullInvocation := newFI } task

||| Generate declarations for given task, unification results, and monomorphic type
monoDecls : Elaboration m => MonoTask -> UniResults -> TypeInfo -> m $ List Decl
monoDecls task uniResults monoTy = do
  let monoTyDecl = monoTy.decl
  logMsg "SpecialiseData" 0 "monoTyDecl : \{show monoTyDecl}"
  let mToPImplDecls = mkMToPImplDecls task uniResults monoTy
  logMsg "SpecialiseData" 0 "mToPImplDecls : \{show mToPImplDecls}"
  let mToPDecls = mkMToPDecls task monoTy
  logMsg "SpecialiseData" 0 "mToP : \{show mToPDecls}"
  multiInjDecls <- mkMultiInjDecls task uniResults monoTy
  logMsg "SpecialiseData" 0 "multiInj : \{show multiInjDecls}"
  multiCongDecls <- mkMultiCongDecls task uniResults monoTy
  logMsg "SpecialiseData" 0 "multiCong : \{show multiCongDecls}"
  castInjDecls <- mkCastInjDecls task uniResults monoTy
  logMsg "SpecialiseData" 0 "castInj : \{show castInjDecls}"
  decEqDecls <- mkDecEqDecls task uniResults monoTy
  logMsg "SpecialiseData" 0 "decEq : \{show decEqDecls}"
  let showDecls = mkShowDecls task uniResults monoTy
  logMsg "SpecialiseData" 0 "Show : \{show showDecls}"
  let eqDecls = mkEqDecls task uniResults monoTy
  logMsg "SpecialiseData" 0 "Eq : \{show eqDecls}"
  let pToMImplDecls = mkPToMImplDecls task uniResults monoTy
  logMsg "SpecialiseData" 0 "pToMImplDecls : \{show pToMImplDecls}"
  let pToMDecls = mkPToMDecls task monoTy
  logMsg "SpecialiseData" 0 "pToM : \{show pToMDecls}"
  pure $ singleton $ INamespace EmptyFC (MkNS [ show task.outputName ]) $
    monoTyDecl :: join
      [ mToPImplDecls
      , mToPDecls
      , multiInjDecls
      , multiCongDecls
      , castInjDecls
      , decEqDecls
      , showDecls
      , eqDecls
      , pToMImplDecls
      , pToMDecls
      ]

||| Perform a specified specialisation
public export
specialiseData :
  TypeTask l =>
  Monad m =>
  Elaboration m =>
  MonadError SpecialisationError m =>
  l ->
  Name ->
  m (TypeInfo, List Decl)
specialiseData taskT outputName = do
  task <- getTask taskT outputName
  task <- prepTask task
  logMsg "SpecialiseData" 0 "New task: \{show task}"
  uniResults <- mapCons (\t,ci => runEitherT $ unifyCon t ci) task
  let (S _) = length $ filter isRight $ uniResults
  | _ => throwError EmptyMonoConError
  let monoTy = mkMonoTy task uniResults
  decls <- monoDecls task uniResults monoTy
  pure (monoTy, decls)


||| Perform a specified monomorphisation and declare the results
public export
specialiseData' : TypeTask l => l -> Name -> Elab ()
specialiseData' taskT outputName = do
  (Right (monoTy, decls)) <-
    runEitherT {m=Elab} {e=SpecialisationError} $
      specialiseData taskT outputName
  | Left err => fail "Specialisation error: \{show err}"
  declare decls

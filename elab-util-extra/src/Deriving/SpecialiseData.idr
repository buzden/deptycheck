module Deriving.SpecialiseData

import public Control.Monad.Reader.Tuple
import public Data.SnocList
import public Derive.Prelude
import public Data.List1
import public Data.Vect
import public Data.List
import public Data.List.Quantifiers
import public Data.Either
import public Data.SortedMap
import public Data.SortedSet
import public Data.SortedMap.Dependent
import public Language.Mk
import public Language.Reflection.Expr
import public Language.Reflection.Syntax.Ops
import public Language.Reflection.TT
import public Language.Reflection.TTImp
import public Language.Reflection.Types.Extra
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
export
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

%runElab derive "SpecialisationError" [Show]

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
  tqArty         : Nat
  tqArgs         : Vect tqArty Arg
  tqRet          : TTImp
  tqArgsNamed    : All IsNamedArg tqArgs
  ||| Unification task type
  taskType       : TTImp
  ttArty         : Nat
  ttArgs         : Vect ttArty Arg
  ttArgsNamed    : All IsNamedArg ttArgs
  ||| Namespace in which monomorphise was called
  currentNs      : Namespace
  ||| Name of polymorphic type
  typeName       : Name
  ||| Name of monomorphic type
  outputName     : Name
  ||| Invocation of polymorphic type extracted from unification task
  fullInvocation : TTImp
  ||| Polymorphic type's TypeInfo
  polyTy         : TypeInfo
  ||| Proof that all the constructors of the polymorphic type are named
  polyTyNamed    : IsFullyNamedType polyTy

public export
Show MonoTask where
  show (MkMonoTask tq _ _ _ _ tt _ _ _ ns tn on fi pt _) = "MkMonoTask \{show tq} \{show tt} \{show ns} \{show tn} \{show on} \{show fi} <typeinfo> <proof>"

||| Polymorphic type's constructor
(.Con) : MonoTask -> Type
(.Con) task = Con task.polyTy.arty task.polyTy.args

||| Unification result
record UnificationResult where
  constructor MkUR
  ||| Task given to the unifier
  task : UnificationTask
  ||| Dependency graph returned by the unifier
  uniDg : DependencyGraph
  ||| LHS free variable (polymorphic constructor argument) values
  lhsResult : SortedMap Name TTImp
  ||| RHS free variable (monomorphic type argument) values
  rhsResult : SortedMap Name TTImp
  ||| All free variable values
  fullResult : SortedMap Name TTImp
  ||| Order of dependency of free variables without values
  ||| (monomorphic constructor arguments)
  order : List $ Fin uniDg.freeVars

%runElab derive "UnificationResult" [Show]

||| Unification results for the whole type
UniResults : Type
UniResults = List $ Either String UnificationResult

------------------------------
--- NAMESPACE MANIPULATION ---
------------------------------

||| Get namespace in which elaborator script is executed
getCurrentNS : Elaboration m => m Namespace
getCurrentNS = do
  NS nsn _ <- inCurrentNS ""
  | _ => fail "Internal error: inCurrentNS did not return NS"
  pure nsn

||| Prepend namespace into which everything is generated to name
inGenNS : MonoTask -> Name -> Name
inGenNS task (NS (MkNS subs) n) = do
  let MkNS tns = task.currentNs
  NS (MkNS $ subs ++ show task.outputName :: tns) $ dropNS n
inGenNS task n = do
  let MkNS tns = task.currentNs
  NS (MkNS $ show task.outputName :: tns) $ dropNS n

---------------------
--- TASK ANALYSIS ---
---------------------

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
  let (tqArgs, tqRet) = unLambda taskQuote
  let Yes tqArgsNamed = all isNamedArg $ fromList tqArgs
  | _ => fail "Internal error: lambda has unnamed arguments"
  taskType : TTImp <- cleanupNamedHoles <$> quote l
  let (ttArgs, _) = unPi taskType
  let Yes ttArgsNamed = all isNamedArg $ fromList ttArgs
  | _ => fail "Internal error: lambda type has unnamed arguments"
  currentNs <- getCurrentNS
  fullInvocation <- taskInvocation taskQuote
  typeName : Name <- taskTName fullInvocation
  polyTy <- cleanupTypeInfo <$> Types.getInfo' typeName
  let Yes polyTyNamed = isFullyNamedType polyTy
  | _ => fail "Internal error: getInfo' returned a type with unnamed arguments or constructors."
  pure $ MkMonoTask
    { taskQuote
    , tqArty = length tqArgs
    , tqArgs = fromList tqArgs
    , tqRet
    , tqArgsNamed
    , taskType
    , ttArty = length ttArgs
    , ttArgs = fromList ttArgs
    , ttArgsNamed
    , currentNs
    , typeName
    , outputName
    , fullInvocation
    , polyTy
    , polyTyNamed
    }

---------------------------
--- Constructor Mapping ---
---------------------------

allToDPairs : (l : List t) -> All p l -> List (x : t ** p x)
allToDPairs [] [] = []
allToDPairs (x :: xs) (p :: ps) = (x ** p) :: allToDPairs xs ps

||| Run monadic operation on all constructors of monomorphic type
mapCons :
  Monad m =>
  (f : (t : MonoTask) ->
       (pCon : t.Con) ->
       IsFullyNamedCon pCon =>
       m r) ->
  MonoTask ->
  m $ List r
  -- traverse (f task) task.polyTy.cons
mapCons f task = do
  let pt = task.polyTyNamed
  let adp = allToDPairs task.polyTy.cons pt.consAreNamed
  traverse (\(c ** pc) => f task c @{pc}) adp

||| Map over all constructors for which unification succeeded
mapUCons :
  (f : (t : MonoTask) ->
       UnificationResult ->
       (pCon : t.Con) ->
       IsFullyNamedCon pCon =>
       r) ->
  MonoTask ->
  UniResults ->
  List r
mapUCons f t rs = do
  let pt = t.polyTyNamed
  let adp = allToDPairs t.polyTy.cons pt.consAreNamed
  foldMap travA $ zip adp rs
  where
    travA :
      ((con : t.Con ** IsFullyNamedCon con), Either String UnificationResult) ->
      List r
    travA ((con ** prf), Left _) = []
    travA ((con ** prf), Right res) = [f t res con]

||| Map over all pairs of monomorphic and polymorphic constructors
map2UCons :
  (f : (t : MonoTask) ->
       UnificationResult ->
       (mt: TypeInfo) ->
       (pc : t.Con) ->
       IsFullyNamedCon pc =>
       (mc : mt.Con) ->
       IsFullyNamedCon mc =>
       r) ->
  MonoTask ->
  UniResults ->
  (mt : TypeInfo) ->
  IsFullyNamedType mt =>
  List r
map2UCons f t rs mt @{mtp} = do
  let pt = t.polyTyNamed
  let p1 = allToDPairs t.polyTy.cons pt.consAreNamed
  let p2 = allToDPairs mt.cons mtp.consAreNamed
  foldMap travA $ zip p1 $ zip p2 rs
  where
    travA :
      ( (pc : t.Con ** IsFullyNamedCon pc)
      , (mc : mt.Con ** IsFullyNamedCon mc)
      , Either String UnificationResult) ->
      List r
    travA ((con ** cprf), (mcon ** mprf), Right res) = [f t res mt con mcon]
    travA _ = []


||| Run monadic operation on all pairs of monomorphic and polymorphic constructors
map2UConsN :
  (f : (t : MonoTask) ->
       UnificationResult ->
       (mt: TypeInfo) ->
       (con : t.Con) ->
       IsFullyNamedCon con =>
       (mcon : mt.Con) ->
       IsFullyNamedCon mcon =>
       Nat ->
       r) ->
  MonoTask ->
  UniResults ->
  (mt : TypeInfo) ->
  IsFullyNamedType mt =>
  List r
map2UConsN f t rs mt @{mtp} = do
  let pt = t.polyTyNamed
  let p1 = allToDPairs t.polyTy.cons pt.consAreNamed
  let p2 = allToDPairs mt.cons mtp.consAreNamed
  traverseA 0 $ zip p1 (zip p2 rs)
  where
    traverseA :
      Nat ->
      List
        ( (pc : t.Con ** IsFullyNamedCon pc)
        , (mc : mt.Con ** IsFullyNamedCon mc)
        , Either String UnificationResult) ->
      List r
    traverseA n ((_, _, Left _) :: xs) = traverseA (S n) xs
    traverseA n (((con ** pprf), (mcon ** mprf), Right res) :: xs) =
      f t res mt con mcon n :: traverseA (S n) xs
    traverseA n _ = []

-------------------------------
--- Constructor unification ---
-------------------------------

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
unifyCon :
  Elaboration m =>
  (t : MonoTask) ->
  (con : t.Con) ->
  IsFullyNamedCon con =>
  EitherT String m UnificationResult
unifyCon t con = do
  let conRet = appArgs .| var t.typeName .| con.typeArgs
  let uniTask =
    MkUniTask _ con.args %search conRet _ t.tqArgs t.tqArgsNamed t.fullInvocation
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
      , uniDg = uniRes
      , lhsResult = fromList lhsRL
      , rhsResult = fromList rhsRL
      , fullResult = fromList urList
      , order = toList fvOrder
      }

-----------------------------------
--- MONOMORPHIC TYPE GENERATION ---
-----------------------------------

||| Generate argument of a monomorphic constructor
mkMonoArg :
  (t : MonoTask) ->
  (ur : UnificationResult) ->
  Fin (ur.uniDg.freeVars) ->
  (arg : Arg ** IsNamedArg arg)
mkMonoArg t ur fvId = do
  let fvData = index fvId ur.uniDg.fvData
  (MkArg fvData.rig fvData.piInfo (Just fvData.name) fvData.type ** ItIsNamed)

dPairsToAll : Vect l (a : t ** p a) -> (v : Vect l t ** All p v)
dPairsToAll [] = ([] ** [])
dPairsToAll ((x ** p) :: ms) = do
  let (xs ** ps) = dPairsToAll ms
  ((x :: xs) ** (p :: ps))

dPairsToAll' : List (a : t ** p a) -> (v : List t ** All p v)
dPairsToAll' [] = ([] ** [])
dPairsToAll' ((x ** p) :: ms) = do
  let (xs ** ps) = dPairsToAll' ms
  ((x :: xs) ** (p :: ps))

||| Generate a monomorphic constructor
mkMonoCon :
  (newArgs : _) ->
  All IsNamedArg newArgs =>
  (t : MonoTask) ->
  UnificationResult ->
  (con : t.Con) ->
  IsFullyNamedCon con =>
  (con : Con _ newArgs ** IsFullyNamedCon con)
mkMonoCon newArgs t ur pCon = do
  let (args ** allArgs) =
    dPairsToAll $ mkMonoArg t ur <$> Vect.fromList ur.order
  let typeArgs = newArgs.appArgs var ur.fullResult
  (MkCon
    { name = inGenNS t $ dropNS pCon.name
    , arty = _
    , args
    , typeArgs
    } ** allArgs)

||| Generate a monomorphic type
mkMonoTy : MonoTask -> UniResults -> (ti : TypeInfo ** IsFullyNamedType ti)
mkMonoTy t ur = do
  let (cons ** consAreNamed) =
    dPairsToAll' $ mapUCons (mkMonoCon t.ttArgs @{t.ttArgsNamed}) t ur
  (MkTypeInfo
            { name = inGenNS t t.outputName
            , arty = _
            , args = t.ttArgs
            , argNames = map (fromMaybe (UN Underscore) . name) t.ttArgs
            , cons
            } ** ItIsFullyNamed t.ttArgsNamed consAreNamed)

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
mkMToPImplSig : MonoTask -> UniResults -> (mt : TypeInfo) -> IsFullyNamedType mt => TTImp
mkMToPImplSig t urs mt =
  forallMTArgs t $ arg (mt.invoke var empty) .-> t.fullInvocation

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
  (pCon : t.Con) ->
  IsFullyNamedCon pCon =>
  (mCon : mt.Con) ->
  IsFullyNamedCon mCon =>
  Clause
mkMToPImplClause t ur mt con mcon =
  (var "mToPImpl" .$ mcon.invoke bindVar
    (substituteVariables
      (fromList $ argsToBindMap $ toList mcon.args) <$> ur.fullResult))
  .= (con.invoke var ur.fullResult)

||| Generate monomorphic to polimorphic type conversion function declarations
mkMToPImplDecls :
  MonoTask ->
  UniResults ->
  (mt : TypeInfo) ->
  IsFullyNamedType mt =>
  List Decl
mkMToPImplDecls t urs mt @{mtp} = do
  let sig = mkMToPImplSig t urs mt @{mtp}
  let clauses = map2UCons mkMToPImplClause t urs mt
  [ public' "mToPImpl" sig
  , def "mToPImpl" clauses
  ]

||| Generate monomorphic to polimorphic cast signature
mkMToPSig : MonoTask -> (mt : TypeInfo) -> IsFullyNamedType mt => TTImp
mkMToPSig t mt = do
  forallMTArgs t $ `(Cast ~(mt.invoke var empty) ~(t.fullInvocation))

||| Generate monomorphic to polimorphic cast declarations
mkMToPDecls : MonoTask -> (mt : TypeInfo) -> IsFullyNamedType mt => List Decl
mkMToPDecls t mt =
  [ interfaceHint Public "mToP" $ mkMToPSig t mt
  , def "mToP" [ (var "mToP") .= `(MkCast mToPImpl)]
  ]

-----------------------------------
--- MULTIINJECTIVITY DERIVATION ---
-----------------------------------
||| Given a list of arguments, generate a list of aliased arguments
||| and a list of aliases

genArgAliases :
  Elaboration m =>
  (as: Vect l Arg) ->
  All IsNamedArg as =>
  List (Name, Name) ->
  m ((v : Vect l Arg ** All IsNamedArg v), List (Name, Name))
genArgAliases [] lnn = pure (([] ** []), lnn)
genArgAliases @{_} (x :: xs) @{(p :: ps)} lnn = do
  let name = Expr.argName x
  alias <- genSym $ show name
  ((as ** aps), am) <- genArgAliases xs ((name, alias) :: lnn)
  let type = substituteVariables (fromList $ mapSnd var <$> lnn) x.type
  pure ((MkArg x.count x.piInfo (Just alias) type :: as ** ItIsNamed :: aps), am)

||| Given a list of aliased argument pairs, generate a list of equality type
||| for each pair
mkEqualsTuple :
  (v1 : Vect l Arg) ->
  (v2 : Vect l Arg) ->
  All IsNamedArg v1 =>
  All IsNamedArg v2 =>
  TTImp
mkEqualsTuple [] [] = `(MkUnit)
mkEqualsTuple [(a1)] [(a2)] @{a1p :: []} @{a2p :: []} =
  `(~(var $ argName a1) ~=~ ~(var $ argName a2))
mkEqualsTuple (a1 :: a1s) (a2 :: a2s) @{a1p :: a1ps} @{a2p :: a2ps} =
  `(Pair (~(var $ argName a1) ~=~ ~(var $ argName a2)) ~(mkEqualsTuple a1s a2s))

||| Given a list of aliased argument pairs [(a, b), ...], generate a series of
||| named applications: (... {a=a} {b=a})
mkDoubleBinds : SnocList (Arg, Arg) -> TTImp -> TTImp
mkDoubleBinds [<] t = t
mkDoubleBinds (as :< (a1, a2)) t =
  case (a1.name, a2.name) of
    (Just a1n, Just a2n) =>
      mkDoubleBinds as t .! (a1n, bindVar a1n) .! (a2n, bindVar a1n)
    _ => mkDoubleBinds as t

||| Make an argument omega implicit
setMWImplicit : Arg -> Arg
setMWImplicit = { piInfo := ImplicitArg, count := MW }

||| A tuple value of multiple repeating expressons
tupleOfN : Nat -> TTImp -> TTImp
tupleOfN 0 _ = `(Unit)
tupleOfN 1 t = t
tupleOfN (S n) t = `(MkPair ~(t) ~(tupleOfN n t))

||| Map all unmapped variables from the list to their aliases
mergeAliases : SortedMap Name TTImp -> List (Name, Name) -> SortedMap Name TTImp
mergeAliases m = mergeWith (curry fst) m . fromList . map (mapSnd var)

renewProof : (args : Vect l Arg) -> All IsNamedArg args => All IsNamedArg (SpecialiseData.setMWImplicit <$> args)
renewProof [] @{[]} = []
renewProof (x :: xs) @{(p :: ps)} with (x)
  renewProof (x :: xs) @{(p :: ps)} | (MkArg _ _ (Just n) _) =
    ItIsNamed :: renewProof xs

||| Derive multiinjectivity for a polymorphic constructor that has a
||| monomorphic equivalent
mkMultiInjDecl :
  Elaboration m =>
  (t : MonoTask) ->
  UnificationResult ->
  (mt : TypeInfo) ->
  (pCon : t.Con) ->
  IsFullyNamedCon pCon =>
  (mCon : mt.Con) ->
  IsFullyNamedCon mCon =>
  Nat ->
  m $ List Decl
mkMultiInjDecl _ ur _ con mcon i = do
  let n = fromString "mInj\{show i}"
  let ourArgs : Vect mcon.arty Arg
      ourArgs = setMWImplicit <$> mcon.args
  let (S _) = mcon.arty
  | _ => pure []
  let prf : All IsNamedArg ourArgs = renewProof mcon.args
  ((a1 ** ap1), am1) <- genArgAliases ourArgs []
  ((a2 ** ap2), am2) <- genArgAliases ourArgs []
  let lhsCon = substituteVariables (fromList $ mapSnd var <$> am1) $
                con.invoke var $ mergeAliases ur.fullResult am1
  let rhsCon = substituteVariables (fromList $ mapSnd var <$> am2) $
                con.invoke var $ mergeAliases ur.fullResult am2

  let eqs = mkEqualsTuple a1 a2
  let sig =
    flip piAll (toList a1) $ flip piAll (toList a2) $ `((~(lhsCon) ~=~ ~(rhsCon)) -> ~(eqs))
  let lhs = mkDoubleBinds (cast $ toList $ zip a1 a2) (var n) .$ `(Refl)
  pure
    [ public' n sig
    , def n $ singleton $ patClause lhs $ tupleOfN mcon.arty `(Refl)
    ]

||| Derive multiinjectivity for all polymorphic constructors that have
||| a monomorphic equivalent
mkMultiInjDecls :
  Elaboration m => MonoTask -> UniResults -> (mt : TypeInfo) -> IsFullyNamedType mt => m $ List Decl
mkMultiInjDecls t ur monoTy = do
  let s = map2UConsN mkMultiInjDecl t ur monoTy
  join <$> sequence s

----------------------------------
--- MULTICONGRUENCY DERIVATION ---
----------------------------------

||| Derive multicongruency for a monomorphic constructor
|||
||| mCongN : forall argsN, argsN'; conN argsN === conN argsN'
mkMultiCongDecl :
  Elaboration m =>
  (t : MonoTask) ->
  UnificationResult ->
  (mt : TypeInfo) ->
  (pCon : t.Con) ->
  IsFullyNamedCon pCon =>
  (mCon : mt.Con) ->
  IsFullyNamedCon mCon =>
  Nat ->
  m $ List Decl
mkMultiCongDecl _ ur _ _ mcon i = do
  let n = fromString "mCong\{show i}"
  let ourArgs : Vect mcon.arty Arg
      ourArgs = setMWImplicit <$> mcon.args
  let (S _) = mcon.arty
  | _ => pure []
  let prf : All IsNamedArg ourArgs = renewProof mcon.args
  ((a1 ** _), am1) <- genArgAliases ourArgs []
  ((a2 ** _), am2) <- genArgAliases ourArgs []
  let lhsCon = mcon.invoke var $ mergeAliases ur.fullResult am1
  let rhsCon = mcon.invoke var $ mergeAliases ur.fullResult am2
  let eqs = mkEqualsTuple a1 a2
  let sig =
    flip piAll (toList a1) $ flip piAll (toList a2) $ `(~(eqs) -> (~(lhsCon) ~=~ ~(rhsCon)))
  let lhs = mkDoubleBinds (cast $ toList $ zip a1 a2) (var n) .$ tupleOfN mcon.arty `(Refl)
  pure
    [ public' n sig
    , def n $ singleton $ patClause lhs $ `(Refl)
    ]

||| Derive multicongruency for all polymorphic constructors that have
||| a monomorphic equivalent
mkMultiCongDecls :
  Elaboration m => MonoTask -> UniResults -> (mt : TypeInfo) -> IsFullyNamedType mt => m $ List Decl
mkMultiCongDecls t ur monoTy = do
  let s = map2UConsN mkMultiCongDecl t ur monoTy
  join <$> sequence s

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
  (t : MonoTask) ->
  UnificationResult ->
  (mt : TypeInfo) ->
  (con : t.Con) ->
  IsFullyNamedCon con =>
  (mcon : mt.Con) ->
  IsFullyNamedCon mcon =>
  Nat ->
  m Clause
mkCastInjClause (ta1, tam1) (ta2, tam2) n1 n2 _ ur _ _ con n = do
  ((a1 ** _), am1) <- genArgAliases con.args []
  ((a2 ** _), am2) <- genArgAliases con.args []
  let am1' = fromList $ mapSnd bindVar <$> am1
  let am2' = fromList $ mapSnd bindVar <$> am2
  let ures1 = substituteVariables am1' <$> ur.fullResult
  let ures2 = substituteVariables am2' <$> ur.fullResult
  let bta1 = bindTyArgs (cast tam1) ures1 `(castInjImpl)
  let bta2 = bindTyArgs (cast tam2) ures2 bta1
  let lhsCon = con.invoke bindVar $ am1'
  let rhsCon = con.invoke bindVar $ am2'
  let patRhs : TTImp
      patRhs = case (length a1) of
        0 => `(Refl)
        _ => (var $ fromString $ "mCong\{show n}") .$
              ((var $ fromString $ "mInj\{show n}") .$ var "r")
  pure $ bta2 .! (n1, lhsCon) .! (n2, rhsCon) .$ bindVar "r" .= patRhs

||| Derive cast injectivity proof
mkCastInjDecls :
  Elaboration m =>
  MonoTask ->
  UniResults ->
  (mt : TypeInfo) ->
  IsFullyNamedType mt =>
  m $ List Decl
mkCastInjDecls @{_} mt ur ti @{tip} = do
  let prepArgs : Vect ti.arty Arg
      prepArgs = setMWImplicit <$> ti.args
  let prf : All IsNamedArg prepArgs = renewProof ti.args @{tip.argsAreNamed}
  ta1@((a1 ** _), am1) <- genArgAliases prepArgs []
  ta2@((a2 ** _), am2) <- genArgAliases prepArgs []
  xVar <- genSym "x"
  yVar <- genSym "y"
  let mToPVar = var $ inGenNS mt "mToP"
  let mToPImplVar = var $ inGenNS mt "mToPImpl"
  let arg1 = MkArg MW ImplicitArg (Just xVar) $
              ti.invoke var $ fromList $ mapSnd var <$> am1
  let arg2 = MkArg MW ImplicitArg (Just yVar) $
              ti.invoke var $ fromList $ mapSnd var <$> am2
  let eqs =
    `((~(withTyArgs (cast am1) mToPImplVar .$ var xVar)
       ~=~
       ~(withTyArgs (cast am2) $ mToPImplVar .$ var yVar)) ->
        ~(var xVar) ~=~ ~(var yVar))
  castInjImplClauses <-
    sequence $ map2UConsN (mkCastInjClause (toList a1, am1) (toList a2, am2) xVar yVar) mt ur ti
  let tyArgPairs = cast $ toList $ zip ti.argNames ti.argNames
  pure
    [ public' "castInjImpl" $
        flip piAll (toList a1) $ flip piAll (toList a2) $ pi arg1 $ pi arg2 $ eqs
    , def "castInjImpl" castInjImplClauses
    , interfaceHint Public "castInj" $ forallMTArgs mt $
        `(Injective ~(withTyArgs tyArgPairs mToPImplVar))
    , def "castInj" $ singleton $
        bindTyArgs tyArgPairs empty `(castInj) .= `(MkInjective castInjImpl)
    ]

-------------------------------------
--- DECIDABLE EQUALITY DERIVATION ---
-------------------------------------

||| Decidable equality signatures
mkDecEqImplSig : MonoTask -> (mt : TypeInfo) -> IsFullyNamedType mt => TTImp
mkDecEqImplSig mt ti =
  let tInv = ti.invoke var empty
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
  in `(decEqImpl x1 x2)
      .= `(decEqInj {f = ~mToPImpl} $ decEq (~mToPImpl x1) (~mToPImpl x2))


||| Derive decidable equality
mkDecEqDecls :
  Elaboration m =>
  MonoTask ->
  UniResults ->
  (mt : TypeInfo) ->
  IsFullyNamedType mt =>
  m $ List Decl
mkDecEqDecls mt ur ti = do
  pure
    [ public' "decEqImpl" $ mkDecEqImplSig mt ti
    , def "decEqImpl" [ mkDecEqImplClause mt ]
    , interfaceHint Public "decEq'" $ forallMTArgs mt
      `(DecEq ~(mt.fullInvocation) => DecEq ~(ti.invoke var empty))
    , def "decEq'"
      [ `(decEq') .= `((Mk DecEq) ~(var $ inGenNS mt "decEqImpl")) ]
    ]

-----------------------
--- SHOW DERIVATION ---
-----------------------

||| Derive Show implementation via cast
mkShowDecls :
  MonoTask ->
  UniResults ->
  (mt : TypeInfo) ->
  IsFullyNamedType mt =>
  List Decl
mkShowDecls mt ur ti = do
  let mToPImpl = var $ inGenNS mt "mToPImpl"
  [ public' "showImpl" $
    forallMTArgs mt
      `(Show ~(mt.fullInvocation) => ~(ti.invoke var empty) -> String)
  , def "showImpl" [ `(showImpl x) .= `(show $ ~mToPImpl x) ]
  , public' "showPrecImpl" $
    forallMTArgs mt
      `(Show ~(mt.fullInvocation) => Prec -> ~(ti.invoke var empty) -> String)
  , def "showPrecImpl"
    [ `(showPrecImpl p x) .= `(showPrec p $ ~mToPImpl x) ]
  , interfaceHint Public "show'" $ forallMTArgs mt $
    `(Show ~(mt.fullInvocation) => Show ~(ti.invoke var empty))
  , def "show'" [ `(show') .= `(MkShow showImpl showPrecImpl) ]
  ]

---------------------
--- EQ DERIVATION ---
---------------------

||| Derive Eq implementation via cast
mkEqDecls :
  MonoTask ->
  UniResults ->
  (mt : TypeInfo) ->
  IsFullyNamedType mt =>
  List Decl
mkEqDecls mt ur ti = do
  let mToPImpl = var $ inGenNS mt "mToPImpl"
  let tInv = ti.invoke var empty
  [ public' "eqImpl" $
    forallMTArgs mt
      `(Eq ~(mt.fullInvocation) => ~tInv -> ~tInv -> Bool)
  , def "eqImpl" [ `(eqImpl x y) .= `((~mToPImpl x) == (~mToPImpl y)) ]
  , public' "neqImpl" $
    forallMTArgs mt
      `(Eq ~(mt.fullInvocation) => ~tInv -> ~tInv -> Bool)
  , def "neqImpl" [ `(neqImpl x y) .= `((~mToPImpl x) /= (~mToPImpl y)) ]
  , interfaceHint Public "eq'" $ forallMTArgs mt $
    `(Eq ~(mt.fullInvocation) => Eq ~tInv)
  , def "eq'" [ `(eq') .= `(MkEq eqImpl neqImpl) ]
  ]

------------------------------------
--- POLY TO MONO CAST DERIVATION ---
------------------------------------

||| Generate monomorphic to polimorphic type conversion function signature
mkPToMImplSig :
  MonoTask ->
  UniResults ->
  (mt : TypeInfo) ->
  IsFullyNamedType mt =>
  TTImp
mkPToMImplSig t urs mt =
  forallMTArgs t $ arg t.fullInvocation .-> mt.invoke var empty

||| Generate monomorphic to polimorphic type conversion function clause
||| for given constructor
mkPToMImplClause :
  (t : MonoTask) ->
  UnificationResult ->
  (mt : TypeInfo) ->
  (pCon : t.Con) ->
  IsFullyNamedCon pCon =>
  (mCon : mt.Con) ->
  IsFullyNamedCon mCon =>
  Clause
mkPToMImplClause t ur mt con mcon =
  var "pToMImpl" .$ con.invoke bindVar
    (substituteVariables
      (fromList $ argsToBindMap $ toList con.args) <$> ur.fullResult)
    .= mcon.invoke var ur.fullResult

||| Generate monomorphic to polimorphic type conversion function declarations
mkPToMImplDecls :
  MonoTask ->
  UniResults ->
  (mt : TypeInfo) ->
  IsFullyNamedType mt =>
  List Decl
mkPToMImplDecls t urs mt = do
  let sig = mkPToMImplSig t urs mt
  let clauses = map2UCons mkPToMImplClause t urs mt
  [ public' "pToMImpl" sig
  , def "pToMImpl" clauses
  ]

||| Generate monomorphic to polimorphic cast signature
mkPToMSig : MonoTask -> (mt : TypeInfo) -> IsFullyNamedType mt => TTImp
mkPToMSig t mt = do
  forallMTArgs t $ `(Cast ~(t.fullInvocation) ~(mt.invoke var empty))

||| Generate monomorphic to polimorphic cast declarations
mkPToMDecls : MonoTask -> (mt : TypeInfo) -> IsFullyNamedType mt => List Decl
mkPToMDecls t mt =
  [ interfaceHint Public "pToM" $ mkPToMSig t mt
  , def "pToM" [ (var "pToM") .= `(MkCast pToMImpl)]
  ]

||| Alias all monomorphic type's arguments to rule out the possibility
||| of lhs-rhs name collision during unification (and derivation)
prepTask : Elaboration m => MonoTask -> m MonoTask
prepTask task = do
  ((newArgs ** newArgsNamed), am) <-
    genArgAliases @{%search} task.tqArgs @{task.tqArgsNamed} []
  logMsg "Monomorphiser" 0 "generated aliases: \{show am}"
  let wil = substituteVariables (fromList $ mapSnd var <$> am)
  -- let newTTArgs = prepTTArg <$> task.ttArgs
  let newTQ = foldr lam (wil task.tqRet) newArgs
  let newTT = piAll (wil `(Type)) $ toList newArgs
  let newFI = wil task.fullInvocation
  pure $
    { taskQuote := newTQ
    , tqArgs := newArgs
    , tqArgsNamed := newArgsNamed
    , tqRet := wil task.tqRet
    , taskType := newTT
    , fullInvocation := newFI
    } task

||| Generate declarations for given task, unification results, and monomorphic type
monoDecls : Elaboration m => MonoTask -> UniResults -> (mt : TypeInfo) -> IsFullyNamedType mt => m $ List Decl
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
  -- task <- prepTask task
  logMsg "SpecialiseData" 0 "New task: \{show task}"
  uniResults <- mapCons (\t,ci => runEitherT $ unifyCon t ci) task
  let (S _) = length $ filter isRight $ uniResults
  | _ => throwError EmptyMonoConError
  let (monoTy ** monoTyNamed) = mkMonoTy task uniResults
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

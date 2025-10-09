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

-------------------------------------
--- SPECIALISATION TASK INTERFACE ---
-------------------------------------

||| Valid task lambda interface
|||
||| Auto-implemented by any Type or any function that returns Type.
export
interface TaskLambda (t : Type) where

public export
TaskLambda Type

public export
TaskLambda b => TaskLambda (a -> b)

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

-------------------------
--- CUSTOM DATA TYPES ---
-------------------------

||| Specialisation task
record SpecTask where
  constructor MkSpecTask
  ||| Full unification task
  {tqArty        : Nat}
  tqArgs         : Vect tqArty Arg
  tqRet          : TTImp
  {auto tqArgsNamed    : All IsNamedArg tqArgs}
  ||| Unification task type
  {ttArty         : Nat}
  ttArgs         : Vect ttArty Arg
  {auto ttArgsNamed    : All IsNamedArg ttArgs}
  ||| Namespace in which monomorphise was called
  currentNs      : Namespace
  ||| Name of monomorphic type
  outputName     : Name
  ||| Invocation of polymorphic type extracted from unification task
  fullInvocation : TTImp
  ||| Polymorphic type's TypeInfo
  polyTy         : TypeInfo
  ||| Proof that all the constructors of the polymorphic type are named
  {auto polyTyNamed    : IsFullyNamedType polyTy}

public export
Show SpecTask where
  showPrec p t =
    showCon p "SpecTask" $ joinBy "" $
      [ showArg t.tqArgs
      , showArg t.tqRet
      , showArg t.ttArgs
      , showArg t.currentNs
      , showArg t.outputName
      , showArg t.fullInvocation
      , showArg "<polyTy>"
      ]

||| Polymorphic type's constructor
(.Con) : SpecTask -> Type
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

------------------------
--- HELPER FUNCTIONS ---
------------------------

||| Get namespace in which elaborator script is executed
getCurrentNS : Elaboration m => m Namespace
getCurrentNS = do
  NS nsn _ <- inCurrentNS ""
  | _ => fail "Internal error: inCurrentNS did not return NS"
  pure nsn

||| Prepend namespace into which everything is generated to name
inGenNS : SpecTask -> Name -> Name
inGenNS task n = do
  let MkNS tns = task.currentNs
  let newNS = case n of
                   (NS (MkNS subs) n) => subs
                   n => []
  NS (MkNS $ newNS ++ show task.outputName :: tns) $ dropNS n

||| TODO: Refactor into separate module
allToDPairs : (l : List t) -> All p l -> List (x : t ** p x)
allToDPairs [] [] = []
allToDPairs (x :: xs) (p :: ps) = (x ** p) :: allToDPairs xs ps

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

||| Find all variables which have no value
filterEmpty : Vect _ FVData -> List (Name, TTImp)
filterEmpty = foldl myfun []
  where
    myfun : List (Name, TTImp) -> FVData -> List (Name, TTImp)
    myfun xs x =
      case x.value of
        Just val => (x.name, val) :: xs
        Nothing => xs

argsToBindMap : List Arg -> List (Name, TTImp)
argsToBindMap = foldMap (toList . map (\y => (y, bindVar y)) . name)

applyArgAliases :
  (as : Vect l Arg) ->
  All IsNamedArg as =>
  List (Name, Name) ->
  SortedMap Name TTImp ->
  (v : Vect l Arg ** All IsNamedArg v)
applyArgAliases []        @{[]}      ns            ins = ([] ** [])
applyArgAliases (x :: xs) @{p :: ps} ys            ins = do
  let (newIns, newName, ys) : (SortedMap _ _, Name, List (Name, Name))
    = case ys of
           []              => (ins,                   argName x, [])
           ((y, y') :: ys) => (insert y (var y') ins, y',        ys)
  let (rec ** prec) = applyArgAliases xs @{ps} ys newIns
  ((MkArg x.count x.piInfo (Just newName) (substituteVariables newIns x.type) :: rec
    ** %search :: prec))

genAliases' : Elaboration m => (as : Vect l Arg) -> All IsNamedArg as => m $ List (Name, Name)
genAliases' [] = pure []
genAliases' @{_} (x :: xs) @{(p :: ps)} = do
  pure $ (argName x, !(genSym $ show $ Expr.argName x)) :: !(genAliases' @{%search} xs @{ps})

||| Given a list of arguments, generate a list of aliased arguments
||| and a list of aliases
genArgAliases :
  Elaboration m =>
  (as: Vect l Arg) ->
  All IsNamedArg as =>
  m ((v : Vect l Arg ** All IsNamedArg v), List (Name, Name))
genArgAliases as = do
  aliases <- genAliases' as
  pure (applyArgAliases as aliases empty, aliases)

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

||| Create a binding application of aliased arguments
aliasedAppBind : SnocList (Name, Name) -> SortedMap Name TTImp -> TTImp -> TTImp
aliasedAppBind [<] nm t = t
aliasedAppBind (xs :< (n, an)) nm t =
  aliasedAppBind xs nm t .! (an, fromMaybe (bindVar n) $ lookup n nm)

||| Create a non-binding application of aliased arguments
aliasedApp : SnocList (Name, Name) -> TTImp -> TTImp
aliasedApp [<] t = t
aliasedApp (xs :< (n, an)) t =
  aliasedApp xs t .! (n, var an)

---------------------
--- TASK ANALYSIS ---
---------------------

||| Get all the information needed for monomorphisation from task
getTask :
  TaskLambda l =>
  Monad m =>
  Elaboration m =>
  MonadError SpecialisationError m =>
  l ->
  Name ->
  m SpecTask
getTask l' outputName = with Prelude.(>>=) do
  taskQuote : TTImp <- cleanupNamedHoles <$> quote l' --- TODO: alias lambda args
  taskType : TTImp <- cleanupNamedHoles <$> quote l
  let (tqArgs, tqRet) = unLambda taskQuote
  let (IVar _ typeName, _) = unApp tqRet
  | _ => throwError TaskTypeExtractionError
  let Yes tqArgsNamed = all isNamedArg $ fromList tqArgs
  | _ => fail "Internal error: lambda has unnamed arguments"
  ((tqArgs ** tqArgsNamed), tqAlias) <- genArgAliases (fromList tqArgs)
  let tqRet = substituteVariables (fromList $ mapSnd var <$> tqAlias) tqRet
  let (ttArgs, _) = unPi taskType
  let Yes ttArgsNamed = all isNamedArg $ fromList ttArgs
  | _ => fail "Internal error: lambda type has unnamed arguments"
  let (ttArgs ** ttArgsNamed) = applyArgAliases (fromList ttArgs) tqAlias empty
  currentNs <- getCurrentNS
  polyTy <- cleanupTypeInfo <$> Types.getInfo' typeName
  let Yes polyTyNamed = isFullyNamedType polyTy
  | _ => fail "Internal error: getInfo' returned a type with unnamed arguments or constructors."
  pure $ MkSpecTask
    { tqArgs
    , tqRet
    , tqArgsNamed
    , ttArgs
    , ttArgsNamed
    , currentNs
    , outputName
    , fullInvocation = tqRet --- TODO: intelligent full invocation
    , polyTy
    , polyTyNamed
    }


parameters (t : SpecTask)
  ---------------------------
  --- Constructor Mapping ---
  ---------------------------
  ||| Run monadic operation on all constructors of monomorphic type
  mapCons :
    (f : (pCon : t.Con) ->
         IsFullyNamedCon pCon =>
         r) ->
    List r
  mapCons f = do
    let pt = t.polyTyNamed
    let adp = allToDPairs t.polyTy.cons pt.consAreNamed
    map (\(c ** pc) => f c @{pc}) adp

  ||| Map over all constructors for which unification succeeded
  ||| TODO: Fix logic bug
  mapUCons :
    (f : UnificationResult ->
         (pCon : t.Con) ->
         IsFullyNamedCon pCon =>
         r) ->
    UniResults ->
    List r
  mapUCons f rs = do
    let pt = t.polyTyNamed
    let adp = allToDPairs t.polyTy.cons pt.consAreNamed
    foldMap travA $ zip adp rs
    where
      travA :
        ((con : t.Con ** IsFullyNamedCon con), Either String UnificationResult) ->
        List r
      travA ((con ** prf), Left _) = []
      travA ((con ** prf), Right res) = [f res con]

  ||| Run monadic operation on all pairs of monomorphic and polymorphic constructors
  ||| TODO: leave only this
  map2UConsN :
    (f : UnificationResult ->
         (mt: TypeInfo) ->
         (con : t.Con) ->
         IsFullyNamedCon con =>
         (mcon : mt.Con) ->
         IsFullyNamedCon mcon =>
         Nat ->
         r) ->
    UniResults ->
    (mt : TypeInfo) ->
    IsFullyNamedType mt =>
    List r
  map2UConsN f rs mt @{mtp} = do
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
        f res mt con mcon n :: traverseA (S n) xs
      traverseA n _ = []

-------------------------------
--- Constructor unification ---
-------------------------------

  ||| Run unification for a given polymorphic constructor
  unifyCon :
    Elaboration m =>
    MonadError String m =>
    (con : t.Con) ->
    IsFullyNamedCon con =>
    m UnificationResult
  unifyCon con = do
    let conRet = appArgs .| var t.polyTy.name .| con.typeArgs
    let uniTask =
      MkUniTask _ con.args %search conRet _ t.tqArgs t.tqArgsNamed t.fullInvocation
    logMsg "SpecialiseData" 0 "Unifier task: \{show uniTask}"
    Right uniRes <- tryError $ unifyWithCompiler uniTask
    | Left err => do
      logMsg "SpecialiseData" 0 "Unifier failed: \{err}"
      throwError err
    logMsg "SpecialiseData" 0 "Unifier returned: \{show uniRes}"
    let fvOrder = flattenEmpties uniRes
    logMsg "SpecialiseData" 0 "Arguments: \{show fvOrder}"
    let urList = filterEmpty uniRes.fvData
    logMsg "SpecialiseData" 0 "FullResult: \{show urList}"
    let (lhsRL, rhsRL) = List.splitAt con.arty urList
    pure $
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
    (ur : UnificationResult) ->
    Fin (ur.uniDg.freeVars) ->
    (arg : Arg ** IsNamedArg arg)
  mkMonoArg ur fvId = do
    let fvData = index fvId ur.uniDg.fvData
    (MkArg fvData.rig fvData.piInfo (Just fvData.name) fvData.type ** ItIsNamed)

  ||| Generate a monomorphic constructor
  mkMonoCon :
    (newArgs : _) ->
    All IsNamedArg newArgs =>
    UnificationResult ->
    (con : t.Con) ->
    IsFullyNamedCon con =>
    (con : Con _ newArgs ** IsFullyNamedCon con)
  mkMonoCon newArgs ur pCon = do
    let (args ** allArgs) =
      dPairsToAll $ mkMonoArg ur <$> Vect.fromList ur.order
    let typeArgs = newArgs.appArgs var ur.fullResult
    (MkCon
      { name = inGenNS t $ dropNS pCon.name
      , arty = _
      , args
      , typeArgs
      } ** allArgs)

  ||| Generate a monomorphic type
  mkMonoTy : UniResults -> (ti : TypeInfo ** IsFullyNamedType ti)
  mkMonoTy ur = do
    let (cons ** consAreNamed) =
      dPairsToAll' $ mapUCons (mkMonoCon t.ttArgs @{t.ttArgsNamed}) ur
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

  ||| Generate IPi with implicit type arguments and given return
  forallMTArgs : TTImp -> TTImp
  forallMTArgs = flip (foldr pi) (setMWImplicit <$> t.ttArgs)

  ||| Generate monomorphic to polimorphic type conversion function signature
  mkMToPImplSig : UniResults -> (mt : TypeInfo) -> IsFullyNamedType mt => TTImp
  mkMToPImplSig urs mt =
    forallMTArgs $ arg (mt.invoke var empty) .-> t.fullInvocation

  ||| Generate monomorphic to polimorphic type conversion function clause
  ||| for given constructor
  mkMToPImplClause :
    UnificationResult ->
    (mt : TypeInfo) ->
    (pCon : t.Con) ->
    IsFullyNamedCon pCon =>
    (mCon : mt.Con) ->
    IsFullyNamedCon mCon =>
    Nat ->
    Clause
  mkMToPImplClause ur mt con mcon _ =
    var "mToPImpl" .$
      (mcon.invoke bindVar
        (substituteVariables
          (fromList $ argsToBindMap $ toList mcon.args) <$> ur.fullResult))
    .= (con.invoke var ur.fullResult)

  ||| Generate monomorphic to polimorphic type conversion function declarations
  mkMToPImplDecls :
    UniResults ->
    (mt : TypeInfo) ->
    IsFullyNamedType mt =>
    List Decl
  mkMToPImplDecls urs mt @{mtp} = do
    let sig = mkMToPImplSig urs mt @{mtp}
    let clauses = map2UConsN mkMToPImplClause urs mt
    [ public' "mToPImpl" sig
    , def "mToPImpl" clauses
    ]

  ||| Generate monomorphic to polimorphic cast signature
  mkMToPSig : (mt : TypeInfo) -> IsFullyNamedType mt => TTImp
  mkMToPSig mt = do
    forallMTArgs $ `(Cast ~(mt.invoke var empty) ~(t.fullInvocation))

  ||| Generate monomorphic to polimorphic cast declarations
  mkMToPDecls : (mt : TypeInfo) -> IsFullyNamedType mt => List Decl
  mkMToPDecls mt =
    [ interfaceHint Public "mToP" $ mkMToPSig mt
    , def "mToP" [ (var "mToP") .= `(MkCast mToPImpl)]
    ]

  -----------------------------------
  --- MULTIINJECTIVITY DERIVATION ---
  -----------------------------------
  parameters {auto _ : Elaboration m}
    ||| Derive multiinjectivity for a polymorphic constructor that has a
    ||| monomorphic equivalent
    mkMultiInjDecl :
      UnificationResult ->
      (mt : TypeInfo) ->
      (pCon : t.Con) ->
      IsFullyNamedCon pCon =>
      (mCon : mt.Con) ->
      IsFullyNamedCon mCon =>
      Nat ->
      m $ List Decl
    mkMultiInjDecl ur _ con mcon i = do
      let n = fromString "mInj\{show i}"
      let ourArgs : Vect mcon.arty Arg
          ourArgs = setMWImplicit <$> mcon.args
      let (S _) = mcon.arty
      | _ => pure []
      let prf : All IsNamedArg ourArgs = renewProof mcon.args
      ((a1 ** ap1), am1) <- genArgAliases ourArgs
      ((a2 ** ap2), am2) <- genArgAliases ourArgs
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
      UniResults -> (mt : TypeInfo) -> IsFullyNamedType mt => m $ List Decl
    mkMultiInjDecls ur monoTy = do
      let s = map2UConsN mkMultiInjDecl ur monoTy
      join <$> sequence s

    ----------------------------------
    --- MULTICONGRUENCY DERIVATION ---
    ----------------------------------

    ||| Derive multicongruency for a monomorphic constructor
    |||
    ||| mCongN : forall argsN, argsN'; conN argsN === conN argsN'
    mkMultiCongDecl :
      UnificationResult ->
      (mt : TypeInfo) ->
      (pCon : t.Con) ->
      IsFullyNamedCon pCon =>
      (mCon : mt.Con) ->
      IsFullyNamedCon mCon =>
      Nat ->
      m $ List Decl
    mkMultiCongDecl ur _ _ mcon i = do
      let n = fromString "mCong\{show i}"
      let ourArgs : Vect mcon.arty Arg
          ourArgs = setMWImplicit <$> mcon.args
      let (S _) = mcon.arty
      | _ => pure []
      let prf : All IsNamedArg ourArgs = renewProof mcon.args
      ((a1 ** _), am1) <- genArgAliases ourArgs
      ((a2 ** _), am2) <- genArgAliases ourArgs
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

    ||| Derive multicongruency for all monomorphic constructors
    mkMultiCongDecls :
      UniResults -> (mt : TypeInfo) -> IsFullyNamedType mt => m $ List Decl
    mkMultiCongDecls ur monoTy = do
      let s = map2UConsN mkMultiCongDecl ur monoTy
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
    (con : t.Con) ->
    IsFullyNamedCon con =>
    (mcon : mt.Con) ->
    IsFullyNamedCon mcon =>
    Nat ->
    m Clause
  mkCastInjClause (ta1, tam1) (ta2, tam2) n1 n2 ur _ _ con n = do
    ((a1 ** _), am1) <- genArgAliases con.args
    ((a2 ** _), am2) <- genArgAliases con.args
    let am1' = fromList $ mapSnd bindVar <$> am1
    let am2' = fromList $ mapSnd bindVar <$> am2
    let ures1 = substituteVariables am1' <$> ur.fullResult
    let ures2 = substituteVariables am2' <$> ur.fullResult
    let bta1 = aliasedAppBind (cast tam1) ures1 `(castInjImpl)
    let bta2 = aliasedAppBind (cast tam2) ures2 bta1
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
    UniResults ->
    (mt : TypeInfo) ->
    IsFullyNamedType mt =>
    m $ List Decl
  mkCastInjDecls @{_} ur ti @{tip} = do
    let prepArgs : Vect ti.arty Arg
        prepArgs = setMWImplicit <$> ti.args
    let prf : All IsNamedArg prepArgs = renewProof ti.args @{tip.argsAreNamed}
    ta1@((a1 ** _), am1) <- genArgAliases prepArgs
    ta2@((a2 ** _), am2) <- genArgAliases prepArgs
    xVar <- genSym "x"
    yVar <- genSym "y"
    let mToPVar = var $ inGenNS t "mToP"
    let mToPImplVar = var $ inGenNS t "mToPImpl"
    let arg1 = MkArg MW ImplicitArg (Just xVar) $
                ti.invoke var $ fromList $ mapSnd var <$> am1
    let arg2 = MkArg MW ImplicitArg (Just yVar) $
                ti.invoke var $ fromList $ mapSnd var <$> am2
    let eqs =
      `((~(aliasedApp (cast am1) mToPImplVar .$ var xVar)
         ~=~
         ~(aliasedApp (cast am2) $ mToPImplVar .$ var yVar)) ->
          ~(var xVar) ~=~ ~(var yVar))
    castInjImplClauses <-
      sequence $ map2UConsN (mkCastInjClause (toList a1, am1) (toList a2, am2) xVar yVar) ur ti
    let tyArgPairs = cast $ toList $ zip ti.argNames ti.argNames
    pure
      [ public' "castInjImpl" $
          flip piAll (toList a1) $ flip piAll (toList a2) $ pi arg1 $ pi arg2 $ eqs
      , def "castInjImpl" castInjImplClauses
      , interfaceHint Public "castInj" $ forallMTArgs $
          `(Injective ~(aliasedApp tyArgPairs mToPImplVar))
      , def "castInj" $ singleton $
          aliasedAppBind tyArgPairs empty `(castInj) .= `(MkInjective castInjImpl)
      ]

  -------------------------------------
  --- DECIDABLE EQUALITY DERIVATION ---
  -------------------------------------

  ||| Decidable equality signatures
  mkDecEqImplSig : (mt : TypeInfo) -> IsFullyNamedType mt => TTImp
  mkDecEqImplSig ti =
    let tInv = ti.invoke var empty
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
    UniResults ->
    (mt : TypeInfo) ->
    IsFullyNamedType mt =>
    List Decl
  mkDecEqDecls ur ti = do
    [ public' "decEqImpl" $ mkDecEqImplSig ti
    , def "decEqImpl" [ mkDecEqImplClause ]
    , interfaceHint Public "decEq'" $ forallMTArgs
      `(DecEq ~(t.fullInvocation) => DecEq ~(ti.invoke var empty))
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
    IsFullyNamedType mt =>
    List Decl
  mkShowDecls ur ti = do
    let mToPImpl = var $ inGenNS t "mToPImpl"
    [ public' "showImpl" $
      forallMTArgs
        `(Show ~(t.fullInvocation) => ~(ti.invoke var empty) -> String)
    , def "showImpl" [ `(showImpl x) .= `(show $ ~mToPImpl x) ]
    , public' "showPrecImpl" $
      forallMTArgs
        `(Show ~(t.fullInvocation) => Prec -> ~(ti.invoke var empty) -> String)
    , def "showPrecImpl"
      [ `(showPrecImpl p x) .= `(showPrec p $ ~mToPImpl x) ]
    , interfaceHint Public "show'" $ forallMTArgs $
      `(Show ~(t.fullInvocation) => Show ~(ti.invoke var empty))
    , def "show'" [ `(show') .= `(MkShow showImpl showPrecImpl) ]
    ]

  ---------------------
  --- EQ DERIVATION ---
  ---------------------

  ||| Derive Eq implementation via cast
  mkEqDecls :
    UniResults ->
    (mt : TypeInfo) ->
    IsFullyNamedType mt =>
    List Decl
  mkEqDecls ur ti = do
    let mToPImpl = var $ inGenNS t "mToPImpl"
    let tInv = ti.invoke var empty
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
  --- POLY TO MONO CAST DERIVATION ---
  ------------------------------------

  ||| Generate monomorphic to polimorphic type conversion function signature
  mkPToMImplSig :
    UniResults ->
    (mt : TypeInfo) ->
    IsFullyNamedType mt =>
    TTImp
  mkPToMImplSig urs mt =
    forallMTArgs $ arg t.fullInvocation .-> mt.invoke var empty

  ||| Generate monomorphic to polimorphic type conversion function clause
  ||| for given constructor
  mkPToMImplClause :
    UnificationResult ->
    (mt : TypeInfo) ->
    (pCon : t.Con) ->
    IsFullyNamedCon pCon =>
    (mCon : mt.Con) ->
    IsFullyNamedCon mCon =>
    Nat ->
    Clause
  mkPToMImplClause ur mt con mcon _ =
    var "pToMImpl" .$ con.invoke bindVar
      (substituteVariables
        (fromList $ argsToBindMap $ toList con.args) <$> ur.fullResult)
      .= mcon.invoke var ur.fullResult

  ||| Generate monomorphic to polimorphic type conversion function declarations
  mkPToMImplDecls :
    UniResults ->
    (mt : TypeInfo) ->
    IsFullyNamedType mt =>
    List Decl
  mkPToMImplDecls urs mt = do
    let sig = mkPToMImplSig urs mt
    let clauses = map2UConsN mkPToMImplClause urs mt
    [ public' "pToMImpl" sig
    , def "pToMImpl" clauses
    ]

  ||| Generate monomorphic to polimorphic cast signature
  mkPToMSig : (mt : TypeInfo) -> IsFullyNamedType mt => TTImp
  mkPToMSig mt = do
    forallMTArgs $ `(Cast ~(t.fullInvocation) ~(mt.invoke var empty))

  ||| Generate monomorphic to polimorphic cast declarations
  mkPToMDecls : (mt : TypeInfo) -> IsFullyNamedType mt => List Decl
  mkPToMDecls mt =
    [ interfaceHint Public "pToM" $ mkPToMSig mt
    , def "pToM" [ (var "pToM") .= `(MkCast pToMImpl)]
    ]

  ||| Generate declarations for given task, unification results, and monomorphic type
  monoDecls : Elaboration m => UniResults -> (mt : TypeInfo) -> IsFullyNamedType mt => m $ List Decl
  monoDecls  uniResults monoTy = do
    let monoTyDecl = monoTy.decl
    logMsg "SpecialiseData" 0 "monoTyDecl : \{show monoTyDecl}"
    let mToPImplDecls = mkMToPImplDecls uniResults monoTy
    logMsg "SpecialiseData" 0 "mToPImplDecls : \{show mToPImplDecls}"
    let mToPDecls = mkMToPDecls monoTy
    logMsg "SpecialiseData" 0 "mToP : \{show mToPDecls}"
    multiInjDecls <- mkMultiInjDecls uniResults monoTy
    logMsg "SpecialiseData" 0 "multiInj : \{show multiInjDecls}"
    multiCongDecls <- mkMultiCongDecls uniResults monoTy
    logMsg "SpecialiseData" 0 "multiCong : \{show multiCongDecls}"
    castInjDecls <- mkCastInjDecls uniResults monoTy
    logMsg "SpecialiseData" 0 "castInj : \{show castInjDecls}"
    let decEqDecls = mkDecEqDecls uniResults monoTy
    logMsg "SpecialiseData" 0 "decEq : \{show decEqDecls}"
    let showDecls = mkShowDecls uniResults monoTy
    logMsg "SpecialiseData" 0 "Show : \{show showDecls}"
    let eqDecls = mkEqDecls uniResults monoTy
    logMsg "SpecialiseData" 0 "Eq : \{show eqDecls}"
    let pToMImplDecls = mkPToMImplDecls uniResults monoTy
    logMsg "SpecialiseData" 0 "pToMImplDecls : \{show pToMImplDecls}"
    let pToMDecls = mkPToMDecls monoTy
    logMsg "SpecialiseData" 0 "pToM : \{show pToMDecls}"
    pure $ singleton $ INamespace EmptyFC (MkNS [ show t.outputName ]) $
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
  TaskLambda l =>
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
  uniResults <- Prelude.sequence $ mapCons task (\ci => runEitherT {m} $ unifyCon task ci)
  let (S _) = length $ filter isRight $ uniResults
  | _ => throwError EmptyMonoConError
  let (monoTy ** monoTyNamed) = mkMonoTy task uniResults
  decls <- monoDecls task uniResults monoTy
  pure (monoTy, decls)


||| Perform a specified monomorphisation and declare the results
public export
specialiseData' : TaskLambda l => l -> Name -> Elab ()
specialiseData' taskT outputName = do
  (Right (monoTy, decls)) <-
    runEitherT {m=Elab} {e=SpecialisationError} $
      specialiseData taskT outputName
  | Left err => fail "Specialisation error: \{show err}"
  declare decls

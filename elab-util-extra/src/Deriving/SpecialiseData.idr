module Deriving.SpecialiseData

import Control.Monad.Either
import Control.Monad.Reader.Tuple
import Data.SnocList
import Data.DPair
import Data.List1
import Data.Vect
import Data.List
import Data.List.Quantifiers
import Data.Either
import Data.SortedMap
import Data.SortedSet
import Data.SortedMap.Dependent
import Decidable.Equality
import Derive.Prelude
import Language.Mk
import Language.Reflection.Expr
import Language.Reflection.Logging
import Language.Reflection.Syntax.Ops
import Language.Reflection.TT
import Language.Reflection.TTImp
import Language.Reflection.Types.Extra
import Language.Reflection.Unify
import Language.Reflection.Util
import Language.Reflection.VarSubst
import Syntax.IHateParens

%language ElabReflection

%default total

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

%runElab derive "SpecialisationError" [Show]

-------------------------------
--- SPECIALISAION TASK TYPE ---
-------------------------------

||| Specialisation task
record SpecTask where
  constructor MkSpecTask
  ||| Full unification task
  {tqArty             : Nat}
  tqArgs              : Vect tqArty Arg
  tqRet               : TTImp
  {auto 0 tqArgsNamed : All IsNamedArg tqArgs}
  ||| Unification task type
  {ttArty             : Nat}
  ttArgs              : Vect ttArty Arg
  {auto 0 ttArgsNamed : All IsNamedArg ttArgs}
  ||| Namespace in which monomorphise was called
  currentNs           : Namespace
  ||| Name of monomorphic type
  outputName          : Name
  ||| Invocation of polymorphic type extracted from unification task
  fullInvocation      : TTImp
  ||| Polymorphic type's TypeInfo
  polyTy              : TypeInfo
  ||| Proof that all the constructors of the polymorphic type are named
  {auto 0 polyTyNamed : IsFullyNamedType polyTy}

export
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
  let newNS =
    case n of
       (NS (MkNS subs) n) => subs
       n => []
  NS (MkNS $ newNS ++ show task.outputName :: tns) $ dropNS n

||| Given a sequence of arguments, return list of argument name-BindVar pairs
argsToBindMap : Foldable f => f Arg -> List (Name, TTImp)
argsToBindMap = foldMap (toList . map (\y => (y, bindVar y)) . name)

||| Given a vect of arguments and a list of their aliases, apply aliases to then
applyArgAliases :
  (as : Vect l Arg) ->
  (0 _ : All IsNamedArg as) =>
  List (Name, Name) ->
  SortedMap Name TTImp ->
  Subset (Vect l Arg) (All IsNamedArg)
applyArgAliases []        @{[]}      ns ins = (Element [] [])
applyArgAliases (x :: xs) @{p :: ps} ys ins = do
  let (newIns, newName, ys) : (SortedMap _ _, Name, List (Name, Name)) =
    case ys of
       []              => (ins                  , argName x, [])
       ((y, y') :: ys) => (insert y (var y') ins, y'       , ys)
  let Element rec prec = applyArgAliases xs ys newIns
  Element
    (MkArg x.count x.piInfo (Just newName) (substituteVariables newIns x.type) :: rec)
    (ItIsNamed :: prec)

||| Given a list of arguments, generate a list of aliases for them
genAliases' : Elaboration m => (as : Vect l Arg) -> (0 _ : All IsNamedArg as) => m $ List (Name, Name)
genAliases' [] = pure []
genAliases' @{_} (x :: xs) @{(p :: ps)} = do
  MN _ gn <- genSym $ show $ Expr.argName x
  | _ => fail "Intenal specialiser error: genSym returned non-MS name"
  pure $ (argName x, UN $ Basic $ show (Expr.argName x) ++ show gn) :: !(genAliases' xs)

||| Given a list of arguments, generate a list of aliased arguments
||| and a list of aliases
genArgAliases :
  Elaboration m =>
  (as: Vect l Arg) ->
  (0 _ : All IsNamedArg as) =>
  m (Subset (Vect l Arg) (All IsNamedArg), List (Name, Name))
genArgAliases as = do
  aliases <- genAliases' as
  pure (applyArgAliases as aliases empty, aliases)

||| Given a list of aliased argument pairs, generate a list of equality type
||| for each pair
mkEqualsTuple :
  (v1 : Vect l Arg) ->
  (v2 : Vect l Arg) ->
  (0 _ : All IsNamedArg v1) =>
  (0 _ : All IsNamedArg v2) =>
  TTImp
mkEqualsTuple [] [] = `(MkUnit)
mkEqualsTuple [(a1)] [(a2)] @{a1p :: _} @{a2p :: _} =
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
hideExplicitArg : Arg -> Arg
hideExplicitArg a = { piInfo := if a.piInfo == ExplicitArg then ImplicitArg else a.piInfo } a

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
  (args : Vect l Arg) ->
  (0 _ : All IsNamedArg args) =>
  All IsNamedArg (SpecialiseData.hideExplicitArg <$> args)
hideExplicitArgPreservesNames [] @{[]} = []
hideExplicitArgPreservesNames (x :: xs) @{(p :: ps)} with (x)
  hideExplicitArgPreservesNames (x :: xs) @{(p :: ps)} | (MkArg _ _ (Just n) _) =
    ItIsNamed :: hideExplicitArgPreservesNames xs

hideExplicitArgs : (xs: Vect l Arg) -> (0 _ : All IsNamedArg xs) => (ys: Vect l Arg ** All IsNamedArg ys)
hideExplicitArgs xs @{ps} =
  (hideExplicitArg <$> xs ** hideExplicitArgPreservesNames xs)

||| Create a binding application of aliased arguments
||| binding everything to `(_)
aliasedAppBind : SnocList (Name, Name) -> TTImp -> TTImp
aliasedAppBind [<] t = t
aliasedAppBind (xs :< (n, an)) t =
  aliasedAppBind xs t .! (an, `(_))


||| Create a non-binding application of aliased arguments
aliasedApp : SnocList (Name, Name) -> TTImp -> TTImp
aliasedApp [<] t = t
aliasedApp (xs :< (n, an)) t =
  aliasedApp xs t .! (n, var an)

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

||| Get all the information needed for monomorphisation from task
getTask :
  TaskLambda l =>
  Monad m =>
  Elaboration m =>
  MonadError SpecialisationError m =>
  (0 l' : l) ->
  Name ->
  m SpecTask
getTask l' outputName = with Prelude.(>>=) do
  -- Quote spec lambda
  taskQuote : TTImp <- cleanupNamedHoles <$> quote l'
  let (tqArgs, tqRet) = unLambda taskQuote
  -- Check for unused arguments
  checkArgsUse tqArgs $ usesVariables tqRet
  -- Extract name of polymorphic type
  let (IVar _ typeName, _) = unApp tqRet
  | _ => throwError TaskTypeExtractionError
  -- Prove that all spec lambda arguments are named
  let Yes tqArgsNamed = all isNamedArg $ fromList tqArgs
  | _ => fail "Internal error: lambda has unnamed arguments"
  -- Create aliases for spec lambda's arguments and perform substitution
  (Element tqArgs tqArgsNamed, tqAlias) <- genArgAliases (fromList tqArgs)
  let tqRet = substituteVariables (fromList $ mapSnd var <$> tqAlias) tqRet
  -- Quote spec lambda type
  taskType : TTImp <- cleanupNamedHoles <$> quote l
  let (ttArgs, _) = unPi taskType
  -- Check for partial application in spec
  let True = (length tqArgs == length ttArgs)
  | _ => throwError PartialSpecError
  -- Prove that all spec lambda type's arguments are named
  let Yes ttArgsNamed = all isNamedArg $ fromList ttArgs
  | _ => fail "Internal error: lambda type has unnamed arguments"
  -- Apply aliasing to spec lambda type's info
  let Element ttArgs ttArgsNamed = applyArgAliases (fromList ttArgs) tqAlias empty
  -- Get current namespace
  currentNs <- getCurrentNS
  -- Get polymorphic type's info
  polyTy <- cleanupTypeInfo <$> Types.getInfo' typeName
  -- Prove all its arguments/constructors/constructor arguments are named
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
  --- CONSTRUCTOR MAPPING ---
  ---------------------------
  ||| Run monadic operation on all constructors of monomorphic type
  mapCons :
    (f : (pCon : t.Con) ->
         (0 _ : IsFullyNamedCon pCon) =>
         r) ->
    List r
  mapCons f = do
    let adp = pushIn t.polyTy.cons t.polyTyNamed.consAreNamed
    map (\(Element c pc) => f c) adp

  ||| Map over all constructors for which unification succeeded
  mapUCons :
    (f : UnificationResult ->
         (pCon : t.Con) ->
         (0 _ : IsFullyNamedCon pCon) =>
         r) ->
    UniResults ->
    List r
  mapUCons f rs = do
    let adp = pushIn t.polyTy.cons t.polyTyNamed.consAreNamed
    let f' : List (Subset t.Con IsFullyNamedCon) -> UniResults -> List r
        f' (x :: xs) (Left _ :: ys) = f' xs ys
        f' (Element con prf :: xs) (Right res :: ys) = f res con :: f' xs ys
        f' _ _ = []
    f' adp rs

  ||| Run monadic operation on all pairs of monomorphic and polymorphic constructors
  map2UConsN :
    (f : UnificationResult ->
         (mt: TypeInfo) ->
         (con : t.Con) ->
         (0 _ : IsFullyNamedCon con) =>
         (mcon : mt.Con) ->
         (0 _ : IsFullyNamedCon mcon) =>
         Nat ->
         r) ->
    UniResults ->
    (mt : TypeInfo) ->
    (0 _ : IsFullyNamedType mt) =>
    List r
  map2UConsN f rs mt @{mtp} = do
    let p1 = pushIn t.polyTy.cons t.polyTyNamed.consAreNamed
    let p2 = pushIn mt.cons mtp.consAreNamed
    f' 0 p1 p2 rs
    where
      f' :
        Nat ->
        List (Subset t.Con IsFullyNamedCon) ->
        List (Subset mt.Con IsFullyNamedCon) ->
        UniResults ->
        List r
      f' n (x                :: xs)                       ys  (Left _    :: zs) =
        f' n xs ys zs
      f' n (Element con pprf :: xs) (Element mcon mprf :: ys) (Right res :: zs) =
        f res mt con mcon n :: f' (S n) xs ys zs
      f' _ _ _ _ = []

  -------------------------------
  --- CONSTRUCTOR UNIFICATION ---
  -------------------------------

  covering
  ||| Run unification for a given polymorphic constructor
  unifyCon :
    Elaboration m =>
    MonadError String m =>
    (con : t.Con) ->
    (0 conN : IsFullyNamedCon con) =>
    m UnificationResult
  unifyCon con = logBounds "specialiseData.unifyCon" [t.polyTy, con] $ do
    let conRet = appArgs .| var t.polyTy.name .| con.typeArgs
    let uniTask =
      MkUniTask {lfv=_} con.args conRet
                {rfv=_} t.tqArgs {rhsAreNamed=t.tqArgsNamed} t.fullInvocation
    logPoint {level=DetailedTrace} "specialiseData.unifyCon" [t.polyTy, con] "Unifier task: \{show uniTask}"
    Right uniRes <- tryError $ unifyWithCompiler uniTask
    | Left err => do
      logPoint "specialiseData.unifyCon" [t.polyTy, con] "Unifier failed: \{err}"
      throwError err
    logPoint "specialiseData.unifyCon" [t.polyTy, con] "Unifier succeeded"
    logPoint {level=DetailedTrace} "specialiseData.unifyCon" [t.polyTy, con] "Unifier output: \{show uniRes}"
    pure uniRes

  -----------------------------------
  --- MONOMORPHIC TYPE GENERATION ---
  -----------------------------------

  ||| Generate argument of a monomorphic constructor
  mkMonoArg :
    (ur : UnificationResult) ->
    Fin (ur.uniDg.freeVars) ->
    (Subset Arg IsNamedArg)
  mkMonoArg ur fvId = do
    let fvData = index fvId ur.uniDg.fvData
    let fromLambda = finToNat fvId >= ur.task.lfv
    let rig = if fromLambda then M0 else fvData.rig
    let piInfo = if fromLambda && (fvData.piInfo == ExplicitArg) then ImplicitArg else fvData.piInfo
    (Element (MkArg rig piInfo (Just fvData.name) fvData.type) ItIsNamed)

  ||| Generate a monomorphic constructor
  mkMonoCon :
    (newArgs : _) ->
    (0 _ : All IsNamedArg newArgs) =>
    UnificationResult ->
    (con : t.Con) ->
    (0 _ : IsFullyNamedCon con) =>
    Subset (Con _ newArgs) IsFullyNamedCon
  mkMonoCon newArgs ur pCon = do
    let Element args allArgs =
      pullOut $ mkMonoArg ur <$> Vect.fromList ur.order
    let typeArgs = newArgs.appArgs var ur.fullResult
    (Element (MkCon
      { name = inGenNS t $ dropNS pCon.name
      , arty = _
      , args
      , typeArgs
      }) allArgs)

  ||| Generate a monomorphic type
  mkMonoTy : UniResults -> Subset TypeInfo IsFullyNamedType
  mkMonoTy ur = do
    let Element cons consAreNamed =
      pullOut $ mapUCons (mkMonoCon t.ttArgs @{t.ttArgsNamed}) ur
    (Element (MkTypeInfo
              { name = inGenNS t t.outputName
              , arty = _
              , args = t.ttArgs
              , argNames = map (fromMaybe (UN Underscore) . name) t.ttArgs
              , cons
              }) (ItIsFullyNamed t.ttArgsNamed consAreNamed))

  ------------------------------------
  --- MONO TO POLY CAST DERIVATION ---
  ------------------------------------

  ||| Generate IPi with implicit type arguments and given return
  forallMTArgs : TTImp -> TTImp
  forallMTArgs = flip (foldr pi) (hideExplicitArg <$> t.ttArgs)

  ||| Generate monomorphic to polimorphic type conversion function signature
  mkMToPImplSig : UniResults -> (mt : TypeInfo) -> (0 _ : IsFullyNamedType mt) => TTImp
  mkMToPImplSig urs mt =
    forallMTArgs $ arg (mt.invoke var empty) .-> t.fullInvocation

  ||| Generate monomorphic to polimorphic type conversion function clause
  ||| for given constructor
  mkMToPImplClause :
    UnificationResult ->
    (mt : TypeInfo) ->
    (pCon : t.Con) ->
    (0 _ : IsFullyNamedCon pCon) =>
    (mCon : mt.Con) ->
    (0 _ : IsFullyNamedCon mCon) =>
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
    (0 _ : IsFullyNamedType mt) =>
    List Decl
  mkMToPImplDecls urs mt = do
    let sig = mkMToPImplSig urs mt
    let clauses = map2UConsN mkMToPImplClause urs mt
    [ public' "mToPImpl" sig
    , def "mToPImpl" clauses
    ]

  ||| Generate monomorphic to polimorphic cast signature
  mkMToPSig : (mt : TypeInfo) -> (0 _ : IsFullyNamedType mt) => TTImp
  mkMToPSig mt = do
    forallMTArgs $ `(Cast ~(mt.invoke var empty) ~(t.fullInvocation))

  ||| Generate monomorphic to polimorphic cast declarations
  mkMToPDecls : (mt : TypeInfo) -> (0 _ : IsFullyNamedType mt) => List Decl
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
      (0 _ : IsFullyNamedCon pCon) =>
      (mCon : mt.Con) ->
      (0 _ : IsFullyNamedCon mCon) =>
      Nat ->
      m $ List Decl
    mkMultiInjDecl ur mt con mcon i =
      logBounds "specialiseData.mkMultiInjDecl" [mt, mcon] $ do
        let S _ = mcon.arty
        | _ => pure []
        let n = fromString "mInj\{show i}"
        let (ourArgs ** prf) = hideExplicitArgs mcon.args
        (Element a1 ap1, am1) <- genArgAliases ourArgs
        (Element a2 ap2, am2) <- genArgAliases ourArgs
        let lhsCon = substituteVariables (fromList $ mapSnd var <$> am1) $
                      con.invoke var $ mergeAliases ur.fullResult am1
        let rhsCon = substituteVariables (fromList $ mapSnd var <$> am2) $
                      con.invoke var $ mergeAliases ur.fullResult am2

        let eqs = mkEqualsTuple a1 a2
        let sig =
          flip piAll (toList a1) $
            flip piAll (toList a2) $ `((~(lhsCon) ~=~ ~(rhsCon)) -> ~(eqs))
        let lhs = mkDoubleBinds (cast $ toList $ zip a1 a2) (var n) .$ `(Refl)
        pure
          [ public' n sig
          , def n $ singleton $ patClause lhs $ tupleOfN mcon.arty `(Refl)
          ]

    ||| Derive multiinjectivity for all polymorphic constructors that have
    ||| a monomorphic equivalent
    mkMultiInjDecls :
      UniResults -> (mt : TypeInfo) -> (0 _ : IsFullyNamedType mt) => m $ List Decl
    mkMultiInjDecls ur monoTy =
      logBounds "specialiseData.mkMultiInjDecls" [monoTy] $ do
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
      (0 _ : IsFullyNamedCon pCon) =>
      (mCon : mt.Con) ->
      (0 _ : IsFullyNamedCon mCon) =>
      Nat ->
      m $ List Decl
    mkMultiCongDecl ur mt _ mcon i =
      logBounds "specialiseData.mkMultiCongDecl" [mt, mcon] $ do
        let S _ = mcon.arty
        | _ => pure []
        let n = fromString "mCong\{show i}"
        let (ourArgs ** prf) = hideExplicitArgs mcon.args
        (Element a1 _, am1) <- genArgAliases ourArgs
        (Element a2 _, am2) <- genArgAliases ourArgs
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
      UniResults -> (mt : TypeInfo) -> (0 _ : IsFullyNamedType mt) => m $ List Decl
    mkMultiCongDecls ur monoTy =
      logBounds "specialiseData.mkMultiCongDecls" [monoTy] $ do
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
    (0 _ : IsFullyNamedCon con) =>
    (mcon : mt.Con) ->
    (0 _ : IsFullyNamedCon mcon) =>
    Nat ->
    m Clause
  mkCastInjClause (ta1, tam1) (ta2, tam2) n1 n2 ur mt _ con n =
    logBounds "specialiseData.mkCastInjClause" [mt, con] $ do
      (Element a1 _, am1) <- genArgAliases con.args
      (Element a2 _, am2) <- genArgAliases con.args
      let am1' = fromList $ mapSnd (const `(_)) <$> am1
      let am2' = fromList $ mapSnd (const `(_)) <$> am2
      let ures1 = substituteVariables am1' <$> ur.fullResult
      let ures2 = substituteVariables am2' <$> ur.fullResult
      let bta1 = aliasedAppBind (cast tam1) `(castInjImpl)
      let bta2 = aliasedAppBind (cast tam2) bta1
      let lhsCon = con.invoke bindVar $ am1'
      let rhsCon = con.invoke bindVar $ am1'
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
    (0 _ : IsFullyNamedType mt) =>
    m $ List Decl
  mkCastInjDecls @{_} ur ti @{tip} =
    logBounds "specialiseData.mkCastInjDecls" [ti] $ do
      let (prepArgs ** prf) = hideExplicitArgs ti.args @{tip.argsAreNamed}
      ta1@(Element a1 _, am1) <- genArgAliases prepArgs
      ta2@(Element a2 _, am2) <- genArgAliases prepArgs
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
            aliasedAppBind tyArgPairs `(castInj) .= `(MkInjective castInjImpl)
        ]

  -------------------------------------
  --- DECIDABLE EQUALITY DERIVATION ---
  -------------------------------------

  ||| Decidable equality signatures
  mkDecEqImplSig : (mt : TypeInfo) -> (0 _ : IsFullyNamedType mt) => TTImp
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
    Elaboration m =>
    UniResults ->
    (mt : TypeInfo) ->
    (0 _ : IsFullyNamedType mt) =>
    m $ List Decl
  mkDecEqDecls ur ti = do
    mkDecEq <- var <$> try (getMk DecEq) (fail "Internal specialiser error: getMk failed.")
    pure $
      [ public' "decEqImpl" $ mkDecEqImplSig ti
      , def "decEqImpl" [ mkDecEqImplClause ]
      , interfaceHint Public "decEq'" $ forallMTArgs
        `(DecEq ~(t.fullInvocation) => DecEq ~(ti.invoke var empty))
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
    (0 _ : IsFullyNamedType mt) =>
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
    (0 _ : IsFullyNamedType mt) =>
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
    (0 _ : IsFullyNamedType mt) =>
    TTImp
  mkPToMImplSig urs mt =
    forallMTArgs $ arg t.fullInvocation .-> mt.invoke var empty

  ||| Generate monomorphic to polimorphic type conversion function clause
  ||| for given constructor
  mkPToMImplClause :
    UnificationResult ->
    (mt : TypeInfo) ->
    (pCon : t.Con) ->
    (0 _ : IsFullyNamedCon pCon) =>
    (mCon : mt.Con) ->
    (0 _ : IsFullyNamedCon mCon) =>
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
    (0 _ : IsFullyNamedType mt) =>
    List Decl
  mkPToMImplDecls urs mt = do
    let sig = mkPToMImplSig urs mt
    let clauses = map2UConsN mkPToMImplClause urs mt
    [ public' "pToMImpl" sig
    , def "pToMImpl" clauses
    ]

  ||| Generate monomorphic to polimorphic cast signature
  mkPToMSig : (mt : TypeInfo) -> (0 _ : IsFullyNamedType mt) => TTImp
  mkPToMSig mt = do
    forallMTArgs $ `(Cast ~(t.fullInvocation) ~(mt.invoke var empty))

  ||| Generate monomorphic to polimorphic cast declarations
  mkPToMDecls : (mt : TypeInfo) -> (0 _ : IsFullyNamedType mt) => List Decl
  mkPToMDecls mt =
    [ interfaceHint Public "pToM" $ mkPToMSig mt
    , def "pToM" [ (var "pToM") .= `(MkCast pToMImpl)]
    ]

  -----------------------------
  --- FROMSTRING DERIVATION ---
  -----------------------------

  mkFromStringDecls :
    (mt : TypeInfo) ->
    (0 _ : IsFullyNamedType mt) =>
    List Decl
  mkFromStringDecls ti = do
    let pToMImpl = var $ inGenNS t "pToMImpl"
    let tInv = ti.invoke var empty
    [ public' "fromStringImpl" $
        forallMTArgs
          `(FromString ~(t.fullInvocation) => String -> ~tInv)
    , def "fromStringImpl"
        [ `(fromStringImpl s) .= `(~pToMImpl $ fromString s) ]
    , interfaceHint Public "fromString'" $
        forallMTArgs `(FromString ~(t.fullInvocation) => FromString ~tInv)
    , def "fromString'"
        [ `(fromString') .= `(MkFromString ~(var $ inGenNS t "fromStringImpl")) ]
    ]

  ----------------------
  --- NUM DERIVATION ---
  ----------------------

  mkNumDecls :
    (mt : TypeInfo) ->
    (0 _ : IsFullyNamedType mt) =>
    List Decl
  mkNumDecls ti = do
    let pToMImpl = var $ inGenNS t "pToMImpl"
    let mToPImpl = var $ inGenNS t "mToPImpl"
    let tInv = ti.invoke var empty
    [ public' "numImpl" $
        forallMTArgs
          `(Num ~(t.fullInvocation) => Integer -> ~tInv)
    , def "numImpl"
        [ `(numImpl s) .= `(~pToMImpl $ Num.fromInteger s) ]
    , public' "plusImpl" $
        forallMTArgs
          `(Num ~(t.fullInvocation) => ~tInv -> ~tInv -> ~tInv)
    , def "plusImpl"
        [ `(plusImpl a b ) .= `(~pToMImpl $ (~mToPImpl a) + (~mToPImpl b)) ]
    , public' "starImpl" $
        forallMTArgs
          `(Num ~(t.fullInvocation) => ~tInv -> ~tInv -> ~tInv)
    , def "starImpl"
        [ `(starImpl a b ) .= `(~pToMImpl $ (~mToPImpl a) * (~mToPImpl b)) ]
    , interfaceHint Public "num'" $
        forallMTArgs `(Num ~(t.fullInvocation) => Num ~tInv)
    , def "num'"
        [ `(num') .= `(MkNum ~(var $ inGenNS t "plusImpl")
                             ~(var $ inGenNS t "starImpl")
                             ~(var $ inGenNS t "numImpl"))
        ]
    ]

  ------------------------------------
  --- SPECIALISED TYPE DECLARATION ---
  ------------------------------------

  ||| Generate declarations for given task, unification results, and monomorphic type
  monoDecls : Elaboration m => UniResults -> (mt : TypeInfo) -> (0 _ : IsFullyNamedType mt) => m $ List Decl
  monoDecls  uniResults monoTy = do
    let monoTyDecl = monoTy.decl
    logPoint {level=DetailedTrace} "specialiseData.monoDecls" [monoTy]
      "monoTyDecl : \{show monoTyDecl}"
    let mToPImplDecls = mkMToPImplDecls uniResults monoTy
    logPoint {level=DetailedTrace} "specialiseData.monoDecls" [monoTy]
      "mToPImplDecls : \{show mToPImplDecls}"
    let mToPDecls = mkMToPDecls monoTy
    logPoint {level=DetailedTrace} "specialiseData.monoDecls" [monoTy]
      "mToP : \{show mToPDecls}"
    multiInjDecls <- mkMultiInjDecls uniResults monoTy
    logPoint {level=DetailedTrace} "specialiseData.monoDecls" [monoTy]
      "multiInj : \{show multiInjDecls}"
    multiCongDecls <- mkMultiCongDecls uniResults monoTy
    logPoint {level=DetailedTrace} "specialiseData.monoDecls" [monoTy]
      "multiCong : \{show multiCongDecls}"
    castInjDecls <- mkCastInjDecls uniResults monoTy
    logPoint {level=DetailedTrace} "specialiseData.monoDecls" [monoTy]
      "castInj : \{show castInjDecls}"
    decEqDecls <- mkDecEqDecls uniResults monoTy
    logPoint {level=DetailedTrace} "specialiseData.monoDecls" [monoTy]
      "decEq : \{show decEqDecls}"
    let showDecls = mkShowDecls uniResults monoTy
    logPoint {level=DetailedTrace} "specialiseData.monoDecls" [monoTy]
      "Show : \{show showDecls}"
    let eqDecls = mkEqDecls uniResults monoTy
    logPoint {level=DetailedTrace} "specialiseData.monoDecls" [monoTy]
      "Eq : \{show eqDecls}"
    let pToMImplDecls = mkPToMImplDecls uniResults monoTy
    logPoint {level=DetailedTrace} "specialiseData.monoDecls" [monoTy]
      "pToMImplDecls : \{show pToMImplDecls}"
    let pToMDecls = mkPToMDecls monoTy
    logPoint {level=DetailedTrace} "specialiseData.monoDecls" [monoTy]
      "pToM : \{show pToMDecls}"
    let fromStringDecls = mkFromStringDecls monoTy
    logPoint {level=DetailedTrace} "specialiseData.monoDecls" [monoTy]
      "fromString : \{show fromStringDecls}"
    let numDecls = mkNumDecls monoTy
    logPoint {level=DetailedTrace} "specialiseData.monoDecls" [monoTy]
      "num : \{show numDecls}"
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
        , fromStringDecls
        , numDecls
        ]

---------------------------
--- DATA SPECIALISATION ---
---------------------------

||| Perform a specified specialisation
export
covering
specialiseData :
  TaskLambda l =>
  Monad m =>
  Elaboration m =>
  MonadError SpecialisationError m =>
  (0 taskT : l) ->
  Name ->
  m (TypeInfo, List Decl)
specialiseData taskT outputName = do
  task <- getTask taskT outputName
  logPoint {level=DetailedTrace} "specialiseData" [task.polyTy] "Specialisation task: \{show task}"
  uniResults <- sequence $ mapCons task $ \ci => runEitherT {m} $ unifyCon task ci
  let Element monoTy monoTyNamed = mkMonoTy task uniResults
  decls <- monoDecls task uniResults monoTy
  pure (monoTy, decls)

||| Perform a specified monomorphisation and return a list of declarations
covering
specialiseData'' : Elaboration m => TaskLambda l => (0 taskT: l) -> Name -> m $ List Decl
specialiseData'' taskT outputName = do
  Right (monoTy, decls) <-
    runEitherT {m} {e=SpecialisationError} $
      specialiseData taskT outputName
  | Left err => fail "Specialisation error: \{show err}"
  pure decls

||| Perform a specified monomorphisation and declare the results
export
covering
specialiseData' : Elaboration m => TaskLambda l => (0 taskT: l) -> Name -> m ()
specialiseData' taskT outputName = specialiseData'' taskT outputName >>= declare

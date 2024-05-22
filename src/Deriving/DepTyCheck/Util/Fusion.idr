module Deriving.DepTyCheck.Util.Fusion

import Language.Reflection
import Language.Reflection.TTImp
import Language.Reflection.Derive
import Language.Reflection.Pretty
import Language.Reflection.Compat
import Deriving.DepTyCheck.Util.Reflection

%default total

matchArgs : List Arg -> List Name -> Maybe (List (Name, TTImp))
matchArgs na la = if length na == length la then Just (zip la (map (.type) na)) else Nothing


buildIPi : List (Name, TTImp) -> TTImp
buildIPi l = piAll type (map (\(n, tti) => MkArg MW ExplicitArg (Just n) tti) l)


unifyArgs : TTImp -> TTImp -> Name -> TTImp
unifyArgs   (IVar _ _)      (IVar _ _)        n = var n -- unifyArgs (IVar n) (IVar Prelude.Types.Z) should be Z
unifyArgs l@(IApp _ _ _)    (IVar _ _)        _ = l
unifyArgs (IVar _ _)        r@(IApp _ _ _)    _ = r
unifyArgs l@(IApp _ _ _)    r@(IApp _ _ _)    _ = if l == r then l else type
unifyArgs l@(IPrimVal _ _)  (IVar _ _)        _ = l
unifyArgs (IVar _ _)        r@(IPrimVal _ _)  _ = r
unifyArgs l@(IPrimVal _ _)  r@(IPrimVal _ _)  _ = if l == r then l else type
unifyArgs _                 _                 _ = type -- others TTImp to add?


processArg : TTImp -> Name -> TTImp
processArg (IVar _ (UN (Basic _)))  n = var n
processArg smth                     _ = smth


bindArgs : TTImp -> TTImp
bindArgs (IVar _ (UN (Basic n))) = bindVar n
bindArgs smth                    = smth


alignArgs : List Name -> List (Name, TTImp) -> List (Name, TTImp) -> List (Name, TTImp)
alignArgs zs xs ys = reverse $ alignArgsInner zs [] xs ys where
  alignArgsInner : List Name -> List (Name, TTImp) -> List (Name, TTImp) -> List (Name, TTImp) -> List (Name, TTImp)
  alignArgsInner [] res _ _ = res
  alignArgsInner (zn::zs) res ((xn, xt)::xs) ((yn, yt)::ys) = case (xn == zn, yn == zn) of
    (True , True ) => alignArgsInner zs ((zn, unifyArgs xt yt zn)::res) xs ys
    (True , False) => alignArgsInner zs ((zn, processArg xt zn)::res) xs ((yn, yt)::ys)
    (False, True ) => alignArgsInner zs ((zn, processArg yt zn)::res) ((xn, xt)::xs) ys
    (False, False) => [(zn, var zn)]
  alignArgsInner (zn::zs) res ((xn, xt)::xs) [] = case (xn == zn) of
     True  => alignArgsInner zs ((zn, processArg xt zn)::res) xs []
     False => [(zn, var zn)]
  alignArgsInner (zn::zs) res [] ((yn, yt)::ys) = case (yn == zn) of
     True  => alignArgsInner zs ((zn, processArg yt zn)::res) [] ys
     False => [(zn, var zn)]
  alignArgsInner (zn::zs) res [] [] = [(zn, var zn)]

-- alignArgs : List (Name, TTImp) -> List (Name, TTImp) -> List Name -> List TTImp
-- alignArgs xs ys zs = reverse $ alignArgsInner [] xs ys zs where
--   alignArgsInner : List TTImp -> List (Name, TTImp) -> List (Name, TTImp) -> List Name -> List TTImp
--   alignArgsInner res _ _ [] = res
--   alignArgsInner res ((xn, xt)::xs) ((yn, yt)::ys) (zn::zs) = case (xn == zn, yn == zn) of
--     (True , True ) => alignArgsInner ((unifyArgs xt yt zn)::res) xs ys zs
--     (True , False) => alignArgsInner ((processArg xt zn)::res) xs ((yn, yt)::ys) zs
--     (False, True ) => alignArgsInner ((processArg yt zn)::res) ((xn, xt)::xs) ys zs
--     (False, False) => [var zn]
--   alignArgsInner res ((xn, xt)::xs) [] (zn::zs) = case  (xn == zn) of
--      True  => alignArgsInner ((processArg xt zn)::res) xs [] zs
--      False => [var zn]
--   alignArgsInner res [] ((yn, yt)::ys) (zn::zs) = case (yn == zn) of
--      True  => alignArgsInner ((processArg yt zn)::res) [] ys zs
--      False => [var zn]
--   alignArgsInner res [] [] (zn::zs) = [var zn]

--  index instead of intermediate name
-- Name (List? String), Type (TTImp), Args (List Name)
-- fuseConstrucror :  List Name -> (Con, List Name) -> (Con, List Name) -> List (Name, List TTImp)
fuseConstrucror :  List Name -> (Name, List TTImp, List Name) -> (Name, List TTImp, List Name) -> (Name, List TTImp, List Name)
fuseConstrucror zl (xName, xArgs, xArgNames) (yName, yArgs, yArgNames) = do
  let xyName = joinBy "_" [nameStr xName, nameStr yName]

  let xArgsZipped = sortBy (\(n1, _), (n2, _) => compare n1 n2) $ zip xArgNames xArgs
  let yArgsZipped = sortBy (\(n1, _), (n2, _) => compare n1 n2) $ zip yArgNames yArgs

  let xyAligned = alignArgs zl xArgsZipped yArgsZipped
  let xyArgNames = map (\(names, _) => names) xyAligned
  let xyArgs = map (\(_, args) => args) xyAligned
  let correctlyAligned = (==) Nothing $ find ((==) type) xyArgs

  if correctlyAligned then (UN (Basic xyName), xyArgs, xyArgNames) else (UN (Basic "fail"), [], [])


foldConstructor : TTImp -> List TTImp -> TTImp
foldConstructor = foldl app


splitRhsDef : List TTImp -> TTImp
splitRhsDef []      = type
splitRhsDef (t::[]) = t
splitRhsDef (t::ts) = app (var `{Builtin.MkPair} .$ t) (splitRhsDef ts)

splitRhsClaim : List TTImp -> TTImp
splitRhsClaim []      = type
splitRhsClaim (t::[]) = t
splitRhsClaim (t::ts) = app (var `{Builtin.Pair} .$ t) (splitRhsClaim ts)


splitClauses : TTImp -> List (List String) -> List Clause
splitClauses sc  = map (
  \cs =>
  patClause
  (app sc $ var $ UN $ Basic (joinBy "_" cs))
  (splitRhsDef (map (\c => var (UN $ Basic c)) cs))
  )


splitReturnType : List Name -> List (List Name) -> List TTImp
splitReturnType tnl anll = map
  (\(t, al) => foldConstructor t al) $
  zip (map (var . UN . Basic . nameStr) tnl) (map (map (.bindVar)) anll)


combinations : List (List a) -> List (List a) -- Vect to precisely express number of elements in tuple
combinations l = map reverse $ combinationsInner l [[]] where
  combinationsInner : List (List a) -> List (List a) -> List (List a)
  combinationsInner (xs::xss) rss = combinationsInner xss $ join $ map (\x => map (\rs => x :: rs) rss) xs
  combinationsInner []        rss = rss


-- combinations' : Vect (S $ S n) (List1 a) -> List1 (Vect (S $ S n) a) -- Vect to precisely express number of elements in tuple
-- combinations' l = map reverse $ combinationsInner l [Nil] where
--   combinationsInner : Vect m (List1 a) -> List1 (Vect k a) -> List1 (Vect (m + k) a)
--   combinationsInner (xs::xss) rss = combinationsInner xss $ join $ map (\x => map (\rs => x :: rs) rss) xs
--   combinationsInner Nil       rss = rss



public export
record FusionDecl where
  constructor MkFusionDecl
  dataType    : Decl
  splitClaim  : Decl
  splitDef    : Decl


prepareConArgs : TTImp -> List TTImp
prepareConArgs t = do
  let (_, tApps) = Reflection.unAppAny t
  map getExpr tApps


deriveFusion : List (TypeInfo, List Name) -> Maybe FusionDecl
deriveFusion l = do

  let typeNames = map (\(n, _) => n.name) l
  let typeNamesStr = map nameStr typeNames
  let joinedNames = joinBy "" typeNamesStr
  let fusionTypeName = UN $ Basic joinedNames

  let typeArgs = map (\(ti, la) => matchArgs ti.args la) l
  let typeArgsDefault = map (\ta => case ta of {Just x => x; _ => []}) typeArgs -- should finish with error if any is Nothing
  let checkArgs = sortBy (\(n1, _), (n2, _) => compare n1 n2) $ join typeArgsDefault
  let uniqueArgs = nub checkArgs -- argument types should be same in every type
  let uniqueNames = nub $ sort $ join $ map (\(_, la) => la) l

  let correctDecl = (length uniqueArgs) == (length uniqueNames)
  let typeSignature = buildIPi uniqueArgs

  let consAll = map (\(t, args) => map (\c => (c, args)) t.cons) l
  let consComb = combinations consAll
  let consCombPrepared = map (map (\(con, args) => (con.name, prepareConArgs con.type, args))) consComb
  let preFusedCons = map (\x => foldl (fuseConstrucror uniqueNames) (case x of {
    [] => (UN (Basic "fail"), [], [])
    (a::_) => a}) (drop 1 x)) consCombPrepared
  let filteredFusedCons = filter (\(n, _, _) => n /= UN (Basic "fail")) preFusedCons
  let fusedCons = map (\(cn, lt, _) => mkTy cn (foldConstructor (var fusionTypeName) (map bindArgs lt))) filteredFusedCons

  let splitName = UN $ Basic ("split" ++ joinedNames)
  let argNamesList = map (\(_, anl) => anl) l

  let dataDecl  = iData Export fusionTypeName typeSignature [] fusedCons
  let claimDecl = export' splitName ((arg $
    foldConstructor (var fusionTypeName) (map (.bindVar) uniqueNames)) .->
    splitRhsClaim (splitReturnType typeNames argNamesList))

  let defCases = def splitName $ splitClauses (var splitName) (map (map (\(c, _) => nameStr c.name)) consComb)
  let defImpossible = def splitName [impossibleClause (var splitName .$ implicitTrue)]
  let defDecl   = if (length fusedCons /= 0) then defCases else defImpossible

  if correctDecl then Just (MkFusionDecl dataDecl claimDecl defDecl) else Nothing


buildConFromOther : TTImp -> List (Name, TTImp) -> List Name -> TTImp
buildConFromOther res _  [] = res
buildConFromOther res la (n::ns) = do
  let ma = find (\(na, _) => na == n) la
  case ma of {Nothing => type; Just (_, tt) => buildConFromOther (app res tt) la ns}


declareFusion : List (TypeInfo, List Name) -> Elab (Maybe FusionDecl)
declareFusion l = do
  let derived = deriveFusion l
  case derived of {Just fd => declare [fd.dataType, fd.splitClaim, fd.splitDef]; Nothing => declare []}
  pure $ derived


public export
runFusion : Name -> List Name -> Name -> List Name -> Elab (Maybe FusionDecl)
runFusion x xArgs y yArgs = do
  xTI <- getInfo' x
  yTI <- getInfo' y
  let zipped = [(xTI, xArgs), (yTI, yArgs)]
  declareFusion zipped


-- public export
-- runFusionList : List (Name, List Name) -> ELab (Maybe FusionDecl)
-- runFusionList l = declareFusion $ map (\(n, args) => { do info <- getInfo' n; (info, args)}) l


public export
runFusionThree : Name -> List Name -> Name -> List Name -> Name -> List Name -> Elab (Maybe FusionDecl)
runFusionThree x xArgs y yArgs z zArgs = do
  xTI <- getInfo' x
  yTI <- getInfo' y
  zTI <- getInfo' z
  let zipped = [(xTI, xArgs), (yTI, yArgs), (zTI, zArgs)]
  declareFusion zipped


public export
getFusion : Maybe FusionDecl -> List Decl
getFusion Nothing   = []
getFusion (Just fd) = [(fd.dataType)]


public export
getSplit : Maybe FusionDecl -> List Decl
getSplit Nothing   = []
getSplit (Just fd) = [fd.splitClaim, fd.splitDef]


-- %language ElabReflection

-- decl : List Decl
-- decl = %runElab runFusion `{X} [`{m}, `{n}] `{Y} [`{n}, `{k}]

-- test : IO ()
-- test = putPretty decl

-- TODO: what happens with :doc
-- tests for order of dependent arguments
-- preserve order of args from left to right
-- TODO: fusion for more than 2 types
-- fold fuseConstructor on combinations

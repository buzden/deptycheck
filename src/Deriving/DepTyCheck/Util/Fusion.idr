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
unifyArgs   (IVar _ _)      (IVar _ _)        n = bindVar (show n) -- unifyArgs (IVar n) (IVar Prelude.Types.Z) should be Z
unifyArgs l@(IApp _ _ _)    (IVar _ _)        _ = l
unifyArgs (IVar _ _)        r@(IApp _ _ _)    _ = r
unifyArgs l@(IApp _ _ _)    r@(IApp _ _ _)    _ = if l == r then l else type
unifyArgs l@(IPrimVal _ _)  (IVar _ _)        _ = l
unifyArgs (IVar _ _)        r@(IPrimVal _ _)  _ = r
unifyArgs l@(IPrimVal _ _)  r@(IPrimVal _ _)  _ = if l == r then l else type
unifyArgs _                 _                 _ = type -- others TTImp to add?


processArg : TTImp -> Name -> TTImp
processArg (IVar _ (UN (Basic _)))  n = bindVar (show n)
processArg smth                     _ = smth


alignArgs : List (Name, TTImp) -> List (Name, TTImp) -> List Name -> List TTImp
alignArgs xs ys zs = reverse $ alignArgsInner [] xs ys zs where
  alignArgsInner : List TTImp -> List (Name, TTImp) -> List (Name, TTImp) -> List Name -> List TTImp
  alignArgsInner res _ _ [] = res
  alignArgsInner res ((xn, xt)::xs) ((yn, yt)::ys) (zn::zs) = case (xn == zn, yn == zn) of
    (True , True ) => alignArgsInner ((unifyArgs xt yt zn)::res) xs ys zs
    (True , False) => alignArgsInner ((processArg xt zn)::res) xs ((yn, yt)::ys) zs
    (False, True ) => alignArgsInner ((processArg yt zn)::res) ((xn, xt)::xs) ys zs
    (False, False) => [var zn]
  alignArgsInner res ((xn, xt)::xs) [] (zn::zs) = case  (xn == zn) of
     True  => alignArgsInner ((processArg xt zn)::res) xs [] zs
     False => [var zn]
  alignArgsInner res [] ((yn, yt)::ys) (zn::zs) = case (yn == zn) of
     True  => alignArgsInner ((processArg yt zn)::res) [] ys zs
     False => [var zn]
  alignArgsInner res [] [] (zn::zs) = [var zn]


fuseConstrucror :  List Name -> (Con, List Name, Con, List Name) -> List (Name, List TTImp)
fuseConstrucror zl (xc, xl, yc, yl) = do 
  let xName = xc.name
  let yName = yc.name
  let xyName = joinBy "_" [nameStr xName, nameStr yName]

  let xType = xc.type
  let yType = yc.type

  let (_, xApps) = Reflection.unAppAny xType
  let (_, yApps) = Reflection.unAppAny yType

  let xArgs = map getExpr xApps
  let yArgs = map getExpr yApps

  let xArgsZipped = sortBy (\(n1, _), (n2, _) => compare n1 n2) $ zip xl xArgs
  let yArgsZipped = sortBy (\(n1, _), (n2, _) => compare n1 n2) $ zip yl yArgs

  let xyAligned = alignArgs xArgsZipped yArgsZipped zl
  let correctlyAligned = (==) 0 $ length $ Prelude.List.filter (\xy => xy == (type)) xyAligned

  if correctlyAligned then [(UN (Basic xyName), xyAligned)] else []


foldConstructor : TTImp -> List TTImp -> TTImp
foldConstructor = foldl app


splitRhs : List TTImp -> TTImp
splitRhs tpe = alternative (UniqueDefault $ foldConstructor (var `{Builtin.MkPair}) tpe) [foldConstructor (var `{Builtin.Pair}) tpe, foldConstructor (var `{Builtin.MkPair}) tpe]


splitClauses : TTImp -> List (Con, Con) -> List Clause
splitClauses sc  = map (\(xc, yc) => patClause (app sc $ var $ UN $ Basic (joinBy "_" [nameStr xc.name, nameStr yc.name])) (splitRhs [var (UN $ Basic $ nameStr xc.name), var (UN $ Basic $ nameStr yc.name)]))


splitReturnType : List Name -> List (List Name) -> List TTImp
splitReturnType tnl anll = map (\(t, al) => foldConstructor t al) $ zip (map (var . UN . Basic . nameStr) tnl) (map (map (.bindVar)) anll)


deriveFusion : List (TypeInfo, List Name) -> (List Decl)
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
  let consProduct = [ (xc, xl, yc, yl) | (xt, xl) <- l, (yt, yl) <- l, xt.name < yt.name, xc <- xt.cons, yc <- yt.cons]
  
  let preCons = join $ map (fuseConstrucror uniqueNames) consProduct
  let fusedCons = map (\(cn, lt) => mkTy cn (foldConstructor (var fusionTypeName) lt)) preCons

  let splitName = UN $ Basic ("split" ++ joinedNames)
  let argNamesList = map (\(_, anl) => anl) l

  let dataDecl  = iData Export fusionTypeName typeSignature [] fusedCons
  let claimDecl = export' splitName ((arg $ foldConstructor (var fusionTypeName) (map (.bindVar) uniqueNames)) .-> splitRhs (splitReturnType typeNames argNamesList))
  let defDecl   = def splitName $ splitClauses (var splitName) (map (\(cx, _, cy, _) => (cx, cy)) consProduct)

  if correctDecl then [dataDecl, claimDecl, defDecl] else []


buildConFromOther : TTImp -> List (Name, TTImp) -> List Name -> TTImp
buildConFromOther res _  [] = res
buildConFromOther res la (n::ns) = do
  let ma = find (\(na, _) => na == n) la
  case ma of {Nothing => type; Just (_, tt) => buildConFromOther (app res tt) la ns}


declareFusion : List (TypeInfo, List Name) -> Elab (List Decl)
declareFusion l = do
  let derived = deriveFusion l
  -- logMsg "debug" 0 $ show derived
  declare derived
  pure $ take 1 derived


public export
runFusion : Name -> List Name -> Name -> List Name -> Elab (List Decl)
runFusion x xArgs y yArgs = do
  xTI <- getInfo' x
  yTI <- getInfo' y
  let zipped = [(xTI, xArgs), (yTI, yArgs)]
  declareFusion zipped

-- data X : Type -> Type where
--     MkX : X n
  
-- data Y : Type -> Type where
--     MkY : Y n 

-- %language ElabReflection

data X : Type -> Type -> Type where
    MkX : X m n
  
data Y : Type -> Type -> Type where
    MkY : Y m n

%language ElabReflection

decl : List Decl
decl = %runElab runFusion `{X} [`{m}, `{n}] `{Y} [`{n}, `{k}]

-- decl : List Decl
-- decl = %runElab runFusion `{X} [`{n}] `{Y} [`{n}]

-- splitXY : XY n -> (X n, Y n)
-- splitXY MkX_MkY = (MkX, MkY)

-- TODO: what happens with :doc
-- tests for order of dependent arguments
-- preserve order of args from left to right
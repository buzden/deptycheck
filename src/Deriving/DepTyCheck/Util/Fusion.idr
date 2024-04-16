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
-- buildIPi l = buildIPiInner (reverse l) (type) where
--   buildIPiInner : List (Name, TTImp) -> TTImp -> TTImp
--   buildIPiInner [] res = res
--   buildIPiInner ((n, tt)::xs) res = buildIPiInner xs (IPi EmptyFC MW ExplicitArg (Just n) tt res)


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
  let
    xName = xc.name
    yName = yc.name
    xyName = joinBy "_" [nameStr xName, nameStr yName]

    xType = xc.type
    yType = yc.type

    (_, xApps) = Reflection.unAppAny xType
    (_, yApps) = Reflection.unAppAny yType

    xArgs = map getExpr xApps
    yArgs = map getExpr yApps

    xArgsZipped = sortBy (\(n1, _), (n2, _) => compare n1 n2) $ zip xl xArgs
    yArgsZipped = sortBy (\(n1, _), (n2, _) => compare n1 n2) $ zip yl yArgs

    xyAligned = alignArgs xArgsZipped yArgsZipped zl
    correctlyAligned = (==) 0 $ length $ Prelude.List.filter (\xy => xy == (type)) xyAligned

  if correctlyAligned then [(UN (Basic xyName), xyAligned)] else []


foldConstructor : TTImp -> List TTImp -> TTImp
foldConstructor res [] = res
foldConstructor res (t::ts) = foldConstructor (app res t) ts


deriveFusion : List (TypeInfo, List Name) -> (List Decl, List Name)
deriveFusion l = let
  typeNames = map (\(n, _) => nameStr n.name) l 
  fusionTypeName = UN (Basic $ joinBy "" typeNames)

  typeArgs = map (\(ti, la) => matchArgs ti.args la) l
  typeArgsDefault = map (\ta => case ta of {Just x => x; _ => []}) typeArgs -- should finish with error if any is Nothing
  checkArgs = sortBy (\(n1, _), (n2, _) => compare n1 n2) $ join typeArgsDefault
  uniqueArgs = nub checkArgs -- argument types should be same in every type

  uniqueNames = nub $ sort $ join $ map (\(_, la) => la) l
  -- uniqueNames = map (\(n, _) => n) uniqueArgs

  correctDecl = (length uniqueArgs) == (length uniqueNames)
  typeSignature = buildIPi uniqueArgs
  consProduct = [ (xc, xl, yc, yl) | (xt, xl) <- l, (yt, yl) <- l, xt.name < yt.name, xc <- xt.cons, yc <- yt.cons]

  preCons = join $ map (fuseConstrucror uniqueNames) consProduct
  fusedCons = map (\(cn, lt) => mkTy cn (foldConstructor (var fusionTypeName) lt)) preCons
  
  in if correctDecl then ([ iData Export fusionTypeName typeSignature [] fusedCons ], uniqueNames) else ([], [])


buildConFromOther : TTImp -> List (Name, TTImp) -> List Name -> TTImp
buildConFromOther res _  [] = res
buildConFromOther res la (n::ns) = do
  let ma = find (\(na, _) => na == n) la
  case ma of {Nothing => type; Just (_, tt) => buildConFromOther (app res tt) la ns}


splitFusion : List ITy -> List Name -> List Name -> List Name -> List (ITy, ITy)
-- splitFusion (IData _ _ _ _ (MkData _ _ _ _ cons)) un xn yn = 
splitFusion cs un xn yn = map (splitInner un xn yn) cs where
  splitInner : List Name -> List Name -> List Name -> ITy -> (ITy, ITy)
  splitInner un xn yn (MkTy _ _ cn ct) = do
    let cs  = split ((==) '_') (nameStr cn)
    let xcn = UN $ Basic $ head cs
    let ycn = UN $ Basic $ last cs
    let (_, args) = unApp ct
    let zipped = zip un args
    let xc  = mkTy xcn (buildConFromOther type zipped xn)
    let yc  = mkTy ycn (buildConFromOther type zipped yn)
    (xc, yc)


declareFusion : List (TypeInfo, List Name) -> Elab ()
declareFusion l = do
  let (derived, _) = deriveFusion l
  for_ derived $ logMsg "debug" 0 . interpolate
  declare $ derived

myFlow : List (TypeInfo, List Name) -> List Name -> List Name -> List (ITy, ITy)
myFlow l xn yn = do
  let (derived, un) = deriveFusion l
  let ts = case derived of {[IData _ _ _ (MkData _ _ _ _ cons)] => cons; _ => []}
  splitFusion ts un xn yn


public export
runFusion : Name -> List Name -> Name -> List Name -> Elab ()
runFusion x xArgs y yArgs = do
  xTI <- getInfo' x
  yTI <- getInfo' y
  let zipped = [(xTI, xArgs), (yTI, yArgs)]
  declareFusion zipped


-- data X : Type -> Type -> Type where
--     MkX : X m n
  
-- data Y : Type -> Type -> Type where
--     MkY : Y m n


data X : Nat -> Type where
    MkX : X 1
  
data Y : Nat -> Type where
    MkY : Y 1

%language ElabReflection

%runElab runFusion `{X} [`{n}] `{Y} [`{n}]

-- %language ElabReflection

-- %runElab (runFusion `{X} [`{n}, `{m}] `{Y} [`{n}, `{m}])

-- TODO: what happens with :doc
-- pack test deptycheck fusion
-- tests for order of dependent arguments
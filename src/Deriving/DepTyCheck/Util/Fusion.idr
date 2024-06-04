module Deriving.DepTyCheck.Util.Fusion

import Language.Reflection
import Language.Reflection.TTImp
import Language.Reflection.Derive
import Language.Reflection.Pretty
import Language.Reflection.Compat
import public Deriving.DepTyCheck.Gen
import Deriving.DepTyCheck.Util.Collections
import Deriving.DepTyCheck.Util.Reflection
import Data.Nat

%default total

matchArgs : List Arg -> List Name -> Maybe (List (Name, TTImp))
matchArgs na la = if length na == length la
  then Just (zip la (map (.type) na))
  else Nothing


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
alignArgs zs xs ys = go zs xs ys where
  go : List Name -> List (Name, TTImp) -> List (Name, TTImp) -> List (Name, TTImp)
  go [] _ _ = []
  go (zn::zs) [] [] = []
  go (zn::zs) ((xn, xt)::xs) ((yn, yt)::ys) = case (xn == zn, yn == zn) of
    (True , True ) => (zn, unifyArgs xt yt zn)::(go zs xs ys)
    (True , False) => (zn, processArg xt zn)  ::(go zs xs ((yn, yt)::ys))
    (False, True ) => (zn, processArg yt zn)  ::(go zs ((xn, xt)::xs) ys)
    (False, False) =>                           (go zs ((xn, xt)::xs) ((yn, yt)::ys))
  go (zn::zs) ((xn, xt)::xs) [] = case (xn == zn) of
     True  => (zn, processArg xt zn)::(go zs xs [])
     False =>                         (go zs xs [])
  go (zn::zs) [] ((yn, yt)::ys) = case (yn == zn) of
     True  => (zn, processArg yt zn)::(go zs [] ys)
     False =>                         (go zs [] ys)


fuseConstrucror :  List Name -> (Name, List TTImp, List Name) -> (Name, List TTImp, List Name) -> (Name, List TTImp, List Name)
fuseConstrucror zl (xName, xArgs, xArgNames) (yName, yArgs, yArgNames) = do
  let xyName = joinBy "_" [nameStr xName, nameStr yName]

  let xArgsZipped = sortBy (comparing fst) $ zip xArgNames xArgs
  let yArgsZipped = sortBy (comparing fst) $ zip yArgNames yArgs

  let xyAligned   = alignArgs zl xArgsZipped yArgsZipped
  let xyArgNames  = map fst xyAligned
  let xyArgs      = map snd xyAligned

  let Nothing = find ((==) type) xyArgs
    | Just _ => (UN (Basic "fail"), [], [])

  (UN (Basic xyName), xyArgs, xyArgNames)


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
splitClauses sc = map
  (\cs =>
    patClause
      (app sc $ var $ UN $ Basic (joinBy "_" cs))
      (splitRhsDef (map (\c => var (UN $ Basic c)) cs)))


splitReturnType : List Name -> List (List Name) -> List TTImp
splitReturnType tnl anll = map
  (\(t, al) => foldConstructor t al) $
  zip
    (map (var . UN . Basic . nameStr) tnl)
    (map (map (.bindVar))             anll)


public export
record FusionDecl where
  constructor MkFusionDecl
  dataType    : Decl
  splitClaim  : Decl
  splitDef    : Decl
  genFClaim   : Decl
  genRClaim   : Decl
  genRDef     : Decl


prepareConArgs : TTImp -> List TTImp
prepareConArgs t = do
  let (_, tApps) = Reflection.unAppAny t
  map getExpr tApps


joinNames : List Name -> Name
joinNames = UN . Basic . (joinBy "") . (map nameStr)


genRMkDPair : TTImp -> List Name -> TTImp
genRMkDPair = foldr (\n, acc => var `{MkDPair} .$ n.bindVar .$ acc)


genFDPair : Name -> List (Name, TTImp) -> TTImp
genFDPair n l = foldr
  (\(n, tt), acc => var `{DPair} .$ tt .$ (MkArg MW ExplicitArg (Just n) tt `lam` acc))
  (foldConstructor (var n) (map (var . fst) l))
  l


genFRhsClaim : Name -> List (Name, TTImp) -> TTImp
genFRhsClaim n l = var `{Gen} .$ var `{MaybeEmpty} .$ genFDPair n l


deriveFusion : Vect (2 + n) (TypeInfo, List Name) -> Maybe FusionDecl
deriveFusion l = do
  let typeNames = toList $ map ((.name) . fst) l
  let fusionTypeName = joinNames $ typeNames

  let typeArgs = map (\(ti, la) => matchArgs ti.args la) l
  let False = any isNothing typeArgs
    | True => Nothing

  let uniqueArgs = nub $ (sortBy (comparing fst)) $ join $ catMaybes $ toList typeArgs -- arg types from type signature
  let uniqueNames = nub $ sort $ join $ toList $ map snd l -- names from target type constructor

  let True = length uniqueArgs == length uniqueNames  -- same parameter name could not be associated with different types
    | False => Nothing
  let typeSignature = buildIPi uniqueArgs

  let consPre = map (\(t, args) => (t.cons, args)) l
  let True = all (not . Prelude.null . fst) consPre
    | False => Nothing
  let consML1 = map (\(cons, args) => (toList1' cons, args)) consPre -- how to prove and use toList?
  let consL1  = map (\(cons, args) => case cons of
                  Just x => (x, args)
                  Nothing => ((MkCon (UN (Basic "")) [] type):::[], args)
                ) consML1
  let consAll = map (\(cons, args) => map (\c => (c, args)) cons) consL1
  let consComb = combinations consAll
  let consCombPrepared = map (map (\(con, args) => (con.name, prepareConArgs con.type, args))) consComb
  let preFusedCons = consCombPrepared <&> \x => foldl (fuseConstrucror uniqueNames) (head x) (tail x)
  let filteredFusedCons = filter (((/=) $ UN (Basic "fail")) . fst) $ toList preFusedCons
  let fusedCons = map
                    (\(cn, lt, _) => mkTy cn (foldConstructor (var fusionTypeName) (map bindArgs lt)))
                    filteredFusedCons

  let splitName = UN $ Basic ("split" ++ (nameStr fusionTypeName))
  let argNamesList = toList $ map snd l

  let dataDecl  = iData Export fusionTypeName typeSignature [] fusedCons
  let claimDecl = export' splitName $
                    (arg $ foldConstructor (var fusionTypeName) (map (.bindVar) uniqueNames)) .->
                    splitRhsClaim (splitReturnType typeNames argNamesList)

  let defDecl = if (not $ null fusedCons)
                then def splitName $ splitClauses (var splitName) $
                  toList (map (toList . (map (nameStr . (.name) . fst))) consComb)
                else def splitName [impossibleClause (var splitName .$ implicitTrue)]

  let stub = ILog Nothing
  let genFName = UN $ Basic ("gen" ++ (nameStr fusionTypeName))
  let genFClaim = export' genFName $
                    (MkArg MW ExplicitArg Nothing (var `{Fuel})) .->
                    (genFRhsClaim fusionTypeName uniqueArgs)

  let genRClaim = export' (`{genZ_ultimate}) $
                    (MkArg MW ExplicitArg Nothing (var `{Fuel})) .->
                    (var `{Gen} .$ var `{MaybeEmpty} .$ var `{Z})

  let fusedVarName = toLower $ nameStr fusionTypeName
  let typeVarNames = map (toLower . nameStr) typeNames
  let genRDef = def
                  `{genZ_ultimate}
                  [  var `{genZ_ultimate}
                  .$ bindVar "fl"
                  .= var `{(>>=)}
                  .$ (var genFName .$ var `{fl})
                  .$ (
                      MkArg MW ExplicitArg (Just "{lamc:0}") implicitFalse
                      `lam` iCase {
                        sc = var "{lamc:0}",
                        ty = implicitFalse,
                        clauses =
                          [ genRMkDPair (bindVar fusedVarName) uniqueNames
                          .= iCase {
                              sc = var splitName .$ (var $ UN $ Basic fusedVarName),
                              ty = implicitTrue,
                              clauses =
                                [ (splitRhsDef (map bindVar typeVarNames))
                                .= var `{pure}
                                .$ foldConstructor (var `{MkZ}) (map var uniqueNames ++ map (var . UN . Basic) typeVarNames)
                                ]
                            }
                          ]
                        }
                      )
                  ]

  Just (MkFusionDecl dataDecl claimDecl defDecl genFClaim genRClaim genRDef)


declareFusion : Vect (2 + n) (TypeInfo, List Name) -> Elab (Maybe FusionDecl)
declareFusion l = do
  let derived = deriveFusion l
  -- case derived of
  --   Just fd => declare [fd.dataType, fd.splitClaim, fd.splitDef, fd.genFClaim, fd.genRClaim, fd.genRDef]
  --   Nothing => declare []
  pure $ derived


prepareArgsSolve : Arg -> (Name, List String)
prepareArgsSolve a = do
  let (xt, as) = Reflection.unAppAny a.type
  let xn = case xt of {IVar _ n => n; _ => UN $ Basic "fail"}
  let ts = map getExpr as
  let ns = map (\t => case t of {IBindVar _ n => n; _ => "fail"}) ts
  (xn, ns)


public export
solveDependencies : List Arg -> List (List (Name, List String))
solveDependencies l = go l [] where
  go : List Arg -> List (List (Name, List String)) -> List (List (Name, List String))
  go []      acc = map reverse acc -- SnocList
  go (a::as) acc = go as (merge (prepareArgsSolve a) acc) where
    merge : (Name, List String) -> List (List (Name, List String)) -> List (List (Name, List String))
    merge a []              = [[a]]
    merge (m, as) (rs::rss) = if (any (not . Prelude.null . (intersect as) . snd) rs)
                              then ((m, as)::rs)::rss
                              else rs::(merge (m, as) rss)


public export
runFusion : Name -> List Name -> Name -> List Name -> Elab (Maybe FusionDecl)
runFusion x xArgs y yArgs = do
  xTI <- getInfo' x
  yTI <- getInfo' y
  let zipped = (xTI, xArgs) :: (yTI, yArgs) :: Nil
  declareFusion zipped


public export
runFusionList : Vect (2 + n) (Name, List Name) -> Elab (Maybe FusionDecl)
runFusionList l = do
  l' <- for l $ \(n, args) => (, args) <$> getInfo' n
  declareFusion l'


public export
getFusion : Maybe FusionDecl -> List Decl
getFusion Nothing   = []
getFusion (Just fd) = [(fd.dataType)]


public export
getSplit : Maybe FusionDecl -> List Decl
getSplit Nothing   = []
getSplit (Just fd) = [fd.splitClaim, fd.splitDef]


public export
getGen : Maybe FusionDecl -> List Decl
getGen Nothing = []
getGen (Just fd) = [fd.genFClaim, fd.genRClaim, fd.genRDef]

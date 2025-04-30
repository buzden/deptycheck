module Language.Reflection.Compat.TypeInfo

import Data.SortedMap
import Data.SortedSet

import public Language.Reflection.Compat.Con
import public Language.Reflection.Expr

import Syntax.IHateParens.SortedSet

%default total

||| Returns a type constructor as `Con` by given type
typeCon : TypeInfo -> Con
typeCon ti = MkCon ti.name ti.args type

---------------------------
--- Analysing type info ---
---------------------------

-- Returns a list without duplications
export
allInvolvedTypes : Elaboration m => (minimalRig : Count) -> TypeInfo -> m $ List TypeInfo
allInvolvedTypes minimalRig ti = toList <$> go [ti] empty where
  go : (left : List TypeInfo) -> (curr : SortedMap Name TypeInfo) -> m $ SortedMap Name TypeInfo
  go left curr = do
    let (c::left) = filter (not . isJust . lookup' curr . name) left
      | [] => pure curr
    let next = insert c.name c curr
    args <- atRig M0 $ join <$> for c.args typesOfArg
    cons <- join <$> for c.tyCons typesOfCon
    assert_total $ go (args ++ cons ++ left) next
    where
      atRig : Count -> m (List a) -> m (List a)
      atRig rig act = if rig >= minimalRig then act else pure []

      typesOfExpr : TTImp -> m $ List TypeInfo
      typesOfExpr expr = map (mapMaybe id) $ for (allVarNames expr) $ catch . getInfo'

      typesOfArg : Arg -> m $ List TypeInfo
      typesOfArg arg = atRig arg.count $ typesOfExpr arg.type

      typesOfCon : Con -> m $ List TypeInfo
      typesOfCon con = [| atRig M0 (typesOfExpr con.type) ++ (join <$> for con.args typesOfArg) |]

-- Fails if the given type info does not have all type args named
export
ensureTyArgsNamed : Elaboration m => (ty : TypeInfo) -> m $ AllTyArgsNamed ty
ensureTyArgsNamed ty = do
  let Yes prf = areAllTyArgsNamed ty
    | No _ => fail "Type info for type `\{ty.name}` contains unnamed arguments"
  pure prf

--------------------------
--- Changing type info ---
--------------------------

normaliseCons : Elaboration m => TypeInfo -> m TypeInfo
normaliseCons ty = do
  cons' <- for ty.cons normaliseCon
  pure $ {cons := cons'} ty

---------------------------
--- Names info in types ---
---------------------------

export
record NamesInfoInTypes where
  constructor Names
  types : SortedMap Name TypeInfo
  cons  : SortedMap Name (TypeInfo, Con)
  namesInTypes : SortedMap TypeInfo $ SortedSet Name

lookupByType : NamesInfoInTypes => Name -> Maybe $ SortedSet Name
lookupByType @{tyi} = lookup' tyi.types >=> lookup' tyi.namesInTypes

lookupByCon : NamesInfoInTypes => Name -> Maybe $ SortedSet Name
lookupByCon @{tyi} = concatMap @{Deep} lookupByType . Prelude.toList . concatMap allVarNames' . conSubexprs . snd <=< lookup' tyi.cons

typeByCon : NamesInfoInTypes => Con -> Maybe TypeInfo
typeByCon @{tyi} = map fst . lookup' tyi.cons . name

export
lookupType : NamesInfoInTypes => Name -> Maybe TypeInfo
lookupType @{tyi} = lookup' tyi.types

export
lookupCon : NamesInfoInTypes => Name -> Maybe Con
lookupCon @{tyi} n = snd <$> lookup n tyi.cons
                 <|> typeCon <$> lookup n tyi.types

export
knownTypes : NamesInfoInTypes => SortedMap Name TypeInfo
knownTypes @{tyi} = tyi.types

||| Returns either resolved expression, or a non-unique name and the set of alternatives.
-- We could use `Validated (SortedMap Name $ SortedSet Name) TTImp` as the result, if we depended on `contrib`.
-- NOTICE: this function does not resolve re-export aliases, say, it does not resolve `Prelude.Nil` to `Prelude.Basics.Nil`.
export
resolveNamesUniquely : NamesInfoInTypes => (freeNames : SortedSet Name) -> TTImp -> Either (Name, SortedSet Name) TTImp
resolveNamesUniquely @{tyi} freeNames = do
  let allConsideredNames = keySet tyi.types `union` keySet tyi.cons
  let reverseNamesMap = concatMap (uncurry SortedMap.singleton) $ allConsideredNames.asList >>= \n => allNameSuffixes n <&> (, SortedSet.singleton n)
  mapATTImp' $ \case
    v@(IVar fc n) => if contains n freeNames then id else do
                       let Just resolvedAlts = lookup n reverseNamesMap | Nothing => id
                       let [resolved] = Prelude.toList resolvedAlts
                         | _ => const $ Left (n, resolvedAlts)
                       const $ pure $ IVar fc resolved
    _ => id

Semigroup NamesInfoInTypes where
  Names ts cs nit <+> Names ts' cs' nit' = Names (ts `mergeLeft` ts') (cs `mergeLeft` cs') (nit <+> nit')

Monoid NamesInfoInTypes where
  neutral = Names empty empty empty where
    Eq TypeInfo where (==) = (==) `on` name
    Ord TypeInfo where compare = comparing name

export
hasNameInsideDeep : NamesInfoInTypes => Name -> TTImp -> Bool
hasNameInsideDeep @{tyi} nm = hasInside empty . allVarNames where

  hasInside : (visited : SortedSet Name) -> (toLook : List Name) -> Bool
  hasInside visited []           = False
  hasInside visited (curr::rest) = if curr == nm then True else do
    let new = if contains curr visited then [] else maybe [] Prelude.toList $ lookupByType curr
    -- visited is limited and either growing or `new` is empty, thus `toLook` is strictly less
    assert_total $ hasInside (insert curr visited) (new ++ rest)

export
isRecursive : NamesInfoInTypes => (con : Con) -> {default Nothing containingType : Maybe TypeInfo} -> Bool
isRecursive con = case the (Maybe TypeInfo) $ containingType <|> typeByCon con of
  Just containingType => any (hasNameInsideDeep containingType.name) $ conSubexprs con
  Nothing             => False

-- returns `Nothing` if given name is not a constructor
export
isRecursiveConstructor : NamesInfoInTypes => Name -> Maybe Bool
isRecursiveConstructor @{tyi} n = lookup' tyi.cons n <&> \(ty, con) => isRecursive {containingType=Just ty} con

export
getNamesInfoInTypes : Elaboration m => TypeInfo -> m NamesInfoInTypes
getNamesInfoInTypes ty = go neutral [ty] where

  subexprs : TypeInfo -> List TTImp
  subexprs ty = map type ty.args ++ (ty.cons >>= conSubexprs)

  go : NamesInfoInTypes -> List TypeInfo -> m NamesInfoInTypes
  go tyi []         = pure tyi
  go tyi (ti::rest) = do
    ti <- normaliseCons ti
    let subes = concatMap allVarNames' $ subexprs ti
    new <- map join $ for (Prelude.toList subes) $ \n =>
             if isNothing $ lookupByType n
               then map toList $ catch $ getInfo' n
               else pure []
    let next = { types $= insert ti.name ti
               , namesInTypes $= insert ti subes
               , cons $= mergeLeft $ fromList $ ti.cons <&> \con => (con.name, ti, con)
               } tyi
    assert_total $ go next (new ++ rest)

export
getNamesInfoInTypes' : Elaboration m => TTImp -> m NamesInfoInTypes
getNamesInfoInTypes' expr = do
  let varsFirstOrder = allVarNames expr
  varsSecondOrder <- map concat $ for varsFirstOrder $ \n => do
                       ns <- getType n
                       pure $ SortedSet.insert n $ flip concatMap ns $ \(n', ty) => insert n' $ allVarNames' ty
  tys <- map (mapMaybe id) $ for (Prelude.toList varsSecondOrder) $ catch . getInfo'
  concat <$> Prelude.for tys getNamesInfoInTypes

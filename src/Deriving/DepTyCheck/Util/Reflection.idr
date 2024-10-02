||| `Language.Reflection`-related utilities
module Deriving.DepTyCheck.Util.Reflection

import public Control.Applicative.Const

import public Data.Alternative

import public Data.Fin.Lists
import public Data.Fin.ToFin
import public Data.Fuel
import public Data.Nat1
import public Data.List.Lazy
import public Data.List.Extra
import public Data.These
import public Data.Vect.Dependent
import public Data.Vect.Extra

import public Data.SortedMap
import public Data.SortedMap.Dependent
import public Data.SortedSet

import public Deriving.DepTyCheck.Util.Logging

import public Language.Reflection.Compat
import public Language.Reflection.TTImp
import public Language.Reflection.Pretty

import public Syntax.IHateParens.Function
import public Syntax.IHateParens.List
import public Syntax.IHateParens.SortedSet
import public Syntax.Monad.Logic

import public Text.PrettyPrint.Bernardy

%default total

-----------------------
--- Pretty-printing ---
-----------------------

LayoutOpts : LayoutOpts
LayoutOpts = Opts 152 -- acceptable line length

export
Interpolation TTImp where
  interpolate = render LayoutOpts . pretty

export
Interpolation Decl where
  interpolate = render LayoutOpts . pretty

export
SingleLogPosition Con where
  logPosition con = do
    let fullName = show con.name
    let fullName' = unpack fullName
    maybe fullName (pack . flip drop fullName' . S . finToNat) $ findLastIndex (== '.') fullName'

----------------------------------------------
--- Compiler-based `TTImp` transformations ---
----------------------------------------------

export
normaliseAsType : Elaboration m => TTImp -> m TTImp
normaliseAsType expr = quote !(check {expected=Type} expr)

-- This is a workaround to not to change `elab-util`'s `getInfo'`
export
normaliseCon : Elaboration m => Con -> m Con
normaliseCon orig@(MkCon n args ty) = do
  let whole = piAll ty args
  Just whole <- catch $ normaliseAsType whole
    | Nothing => pure orig -- didn't manage to normalise, e.g. due to private stuff
  let (args', ty) = unPi whole
  -- `quote` may corrupt names, workaround it:
  let args = args `zip` args' <&> \(pre, normd) => {name := pre.name} normd
  pure $ MkCon n args ty

normaliseCons : Elaboration m => TypeInfo -> m TypeInfo
normaliseCons ty = do
  cons' <- for ty.cons normaliseCon
  pure $ {cons := cons'} ty

--------------------------------------------
--- Parsing and rebuilding `TTImp` stuff ---
--------------------------------------------

public export
isImplicit : PiInfo c -> Bool
isImplicit ImplicitArg     = True
isImplicit (DefImplicit x) = True
isImplicit AutoImplicit    = True
isImplicit ExplicitArg     = False

--- `DPair` type parsing and rebuilding stuff ---

public export
unDPair : TTImp -> (List Arg, TTImp)
unDPair (IApp _ (IApp _ (IVar _ `{Builtin.DPair.DPair}) typ) (ILam _ cnt piInfo mbname _ lamTy)) =
    mapFst (MkArg cnt piInfo mbname typ ::) $ unDPair lamTy
unDPair expr = ([], expr)

public export
unDPairUnAlt : TTImp -> Maybe (List Arg, TTImp)
unDPairUnAlt (IAlternative _ _ alts) = case filter (not . null . Builtin.fst) $ unDPair <$> alts of
  [x] => Just x
  _   => Nothing
unDPairUnAlt x = Just $ unDPair x

public export
buildDPair : (rhs : TTImp) -> List (Name, TTImp) -> TTImp
buildDPair = foldr $ \(name, type), res =>
  var `{Builtin.DPair.DPair} .$ type .$ lam (MkArg MW ExplicitArg (Just name) type) res

--- Facilities for managing any kind of function application at once ---

public export
data AnyApp
  = PosApp TTImp
  | NamedApp Name TTImp
  | AutoApp TTImp
  | WithApp TTImp

public export
appArg : Arg -> TTImp -> AnyApp
appArg (MkArg {piInfo=ExplicitArg, _})         expr = PosApp expr
appArg (MkArg {piInfo=ImplicitArg, name, _})   expr = NamedApp (stname name) expr
appArg (MkArg {piInfo=DefImplicit _, name, _}) expr = NamedApp (stname name) expr
appArg (MkArg {piInfo=AutoImplicit, _})        expr = AutoApp expr

public export
getExpr : AnyApp -> TTImp
getExpr $ PosApp e     = e
getExpr $ NamedApp _ e = e
getExpr $ AutoApp e    = e
getExpr $ WithApp e    = e

-- Shallow expression mapping
public export
mapExpr : (TTImp -> TTImp) -> AnyApp -> AnyApp
mapExpr f $ PosApp e     = PosApp $ f e
mapExpr f $ NamedApp n e = NamedApp n $ f e
mapExpr f $ AutoApp e    = AutoApp $ f e
mapExpr f $ WithApp e    = WithApp $ f e

public export
unAppAny : TTImp -> (TTImp, List AnyApp)
unAppAny = runTR [] where
  runTR : List AnyApp -> TTImp -> (TTImp, List AnyApp)
  runTR curr $ IApp      _ lhs   rhs = runTR (PosApp rhs     :: curr) lhs
  runTR curr $ INamedApp _ lhs n rhs = runTR (NamedApp n rhs :: curr) lhs
  runTR curr $ IAutoApp  _ lhs   rhs = runTR (AutoApp rhs    :: curr) lhs
  runTR curr $ IWithApp  _ lhs   rhs = runTR (WithApp rhs    :: curr) lhs
  runTR curr lhs                     = (lhs, curr)

public export
reAppAny1 : TTImp -> AnyApp -> TTImp
reAppAny1 l $ PosApp e     = app l e
reAppAny1 l $ NamedApp n e = namedApp l n e
reAppAny1 l $ AutoApp e    = autoApp l e
reAppAny1 l $ WithApp e    = IWithApp EmptyFC l e

public export %inline
reAppAny : Foldable f => TTImp -> f AnyApp -> TTImp
reAppAny = foldl reAppAny1

--- Specific expressions building helpers ---

public export
appFuel : (topmost : Name) -> (fuel : TTImp) -> TTImp
appFuel = app . var

public export
liftList : Foldable f => f TTImp -> TTImp
liftList = foldr (\l, r => `(~l :: ~r)) `([])

export
liftWeight1 : TTImp
liftWeight1 = `(Data.Nat1.one)

namespace CompiletimeLabel

  public export
  data CTLabel = MkCTLabel TTImp

  public export
  FromString CTLabel where
    fromString = MkCTLabel . primVal . Str

  public export
  Semigroup CTLabel where
    MkCTLabel l <+> MkCTLabel r = MkCTLabel `(~l ++ ~r)

  public export
  Monoid CTLabel where
    neutral = ""

  namespace FromString
    public export %inline
    (.label) : String -> CTLabel
    (.label) = fromString

  namespace FromTTImp
    public export %inline
    (.label) : TTImp -> CTLabel
    (.label) = MkCTLabel

export
labelGen : (desc : CTLabel) -> TTImp -> TTImp
labelGen (MkCTLabel desc) expr = `(Test.DepTyCheck.Gen.label (fromString ~desc) ~expr)

export
callOneOf : (desc : CTLabel) -> List TTImp -> TTImp
callOneOf desc [v]      = labelGen desc v
callOneOf desc variants = labelGen desc $ `(Test.DepTyCheck.Gen.oneOf {em=MaybeEmpty}) .$ liftList variants

-- List of weights and subgenerators
export
callFrequency : (desc : CTLabel) -> List (TTImp, TTImp) -> TTImp
callFrequency _    [(_, v)] = v
callFrequency desc variants = labelGen desc $ var `{Test.DepTyCheck.Gen.frequency} .$
                                liftList (variants <&> \(freq, subgen) => var `{Builtin.MkPair} .$ freq .$ subgen)

-- TODO to think of better placement for this function; this anyway is intended to be called from the derived code.
public export
leftDepth : Fuel -> Nat1
leftDepth = go 1 where
  go : Nat1 -> Fuel -> Nat1
  go n Dry      = n
  go n (More x) = go (succ n) x

export
isSimpleBindVar : TTImp -> Bool
isSimpleBindVar $ IBindVar {} = True
isSimpleBindVar _             = False

export
callCon : (con : Con) -> Vect con.args.length TTImp -> TTImp
callCon con = reAppAny (var con.name) . toList . mapI (appArg . index' con.args)

export
outmostFuelArg : Name
outmostFuelArg = UN $ Basic "^outmost-fuel^" -- I'm using a name containing chars that cannot be present in the code parsed from the Idris frontend

||| Returns unnamespaced name and list of all namespaces stored in direct order
|||
||| Say, for `Data.Vect.Vect` it would return (["Data", "Vect"], `{Vect}).
unNS : Name -> (List String, Name)
unNS (NS (MkNS revNSs) nm) = mapFst (reverse revNSs ++) $ unNS nm
unNS (DN _ nm)             = unNS nm
unNS nm                    = ([], nm)

||| Returns all names that are suffixes of a given name (incuding the original name itself).
|||
||| For example, for the name `Data.Vect.Vect` suffixes set would include
||| `Data.Vect.Vect`, `Vect.Vect` and `Vect`.
allNameSuffixes : Name -> List Name
allNameSuffixes nm = do
  let (nss, n) = unNS nm
  tails nss <&> \case
    [] => n
    ns => NS (MkNS $ reverse ns) n

export
isNamespaced : Name -> Bool
isNamespaced = not . null . fst . unNS

---------------------------------------------------
--- Working around primitive and special values ---
---------------------------------------------------

primTypeInfo : String -> TypeInfo
primTypeInfo s = MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic s) [] []

export
typeInfoForPrimType : PrimType -> TypeInfo
typeInfoForPrimType IntType     = primTypeInfo "Int"
typeInfoForPrimType IntegerType = primTypeInfo "Integer"
typeInfoForPrimType Int8Type    = primTypeInfo "Int8"
typeInfoForPrimType Int16Type   = primTypeInfo "Int16"
typeInfoForPrimType Int32Type   = primTypeInfo "Int32"
typeInfoForPrimType Int64Type   = primTypeInfo "Int64"
typeInfoForPrimType Bits8Type   = primTypeInfo "Bits8"
typeInfoForPrimType Bits16Type  = primTypeInfo "Bits16"
typeInfoForPrimType Bits32Type  = primTypeInfo "Bits32"
typeInfoForPrimType Bits64Type  = primTypeInfo "Bits64"
typeInfoForPrimType StringType  = primTypeInfo "String"
typeInfoForPrimType CharType    = primTypeInfo "Char"
typeInfoForPrimType DoubleType  = primTypeInfo "Double"
typeInfoForPrimType WorldType   = primTypeInfo "%World"

export
typeInfoForTypeOfTypes : TypeInfo
typeInfoForTypeOfTypes = primTypeInfo "Type"

export
extractTargetTyExpr : TypeInfo -> TTImp
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "Int"    ) [] [] = primVal $ PrT IntType
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "Integer") [] [] = primVal $ PrT IntegerType
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "Int8"   ) [] [] = primVal $ PrT Int8Type
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "Int16"  ) [] [] = primVal $ PrT Int16Type
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "Int32"  ) [] [] = primVal $ PrT Int32Type
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "Int64"  ) [] [] = primVal $ PrT Int64Type
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "Bits8"  ) [] [] = primVal $ PrT Bits8Type
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "Bits16" ) [] [] = primVal $ PrT Bits16Type
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "Bits32" ) [] [] = primVal $ PrT Bits32Type
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "Bits64" ) [] [] = primVal $ PrT Bits64Type
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "String" ) [] [] = primVal $ PrT StringType
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "Char"   ) [] [] = primVal $ PrT CharType
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "Double" ) [] [] = primVal $ PrT DoubleType
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "%World" ) [] [] = primVal $ PrT WorldType
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "Type"   ) [] [] = type
extractTargetTyExpr ti = var ti.name

||| Returns a type constructor as `Con` by given type
typeCon : TypeInfo -> Con
typeCon ti = MkCon ti.name ti.args type

------------------------------------
--- Analysis of type definitions ---
------------------------------------

||| Derives function `A -> B` where `A` is determined by the given `TypeInfo`, `B` is determined by `retTy`
|||
||| For each constructor of `A` the `matcher` function is applied and its result (of type `B`) is used as a result.
||| Currently, `B` must be a non-dependent type.
export
deriveMatchingCons : (retTy : TTImp) -> (matcher : Con -> TTImp) -> (funName : Name) -> TypeInfo -> List Decl
deriveMatchingCons retTy matcher funName ti = do
  let claim = do
    let tyApplied = reAppAny (var ti.name) $ ti.args <&> \arg => appArg arg $ var $ argName arg
    let sig = foldr
                (pi . {count := M0, piInfo := ImplicitArg})
                `(~tyApplied -> ~retTy)
                ti.args
    private' funName sig
  let body = do
    let matchCon = \con => reAppAny (var con.name) $ con.args <&> flip appArg implicitTrue
    def funName $ ti.cons <&> \con =>
      patClause (var funName .$ matchCon con) $ matcher con
  [claim, body]

public export
conSubexprs : Con -> List TTImp
conSubexprs con = map type con.args ++ (map getExpr $ snd $ unAppAny con.type)

export
ensureTyArgsNamed : Elaboration m => (ty : TypeInfo) -> m $ AllTyArgsNamed ty
ensureTyArgsNamed ty = do
  let Yes prf = areAllTyArgsNamed ty
    | No _ => fail "DepTyCheck blames the compiler: type info for type `\{ty.name}` contains unnamed arguments"
  pure prf

-------------------------------------------------
--- Syntactic analysis of `TTImp` expressions ---
-------------------------------------------------

-- fails is given names are not types
public export
isSameTypeAs : Name -> Name -> Elab Bool
isSameTypeAs checked expected = let eq = (==) `on` name in [| getInfo' checked `eq` getInfo' expected |]

export
nameConformsTo : (cand, origin : Name) -> Bool
nameConformsTo cand origin = do
  let (cns, cn) = simplify cand
  let (ons, on) = simplify origin
  cn == on && (cns `isPrefixOf` ons) -- notice that namespaces are stored in the reverse order
  where
    simplify : Name -> (List String, Name)
    simplify (NS (MkNS ns) nm) = mapFst (++ ns) $ simplify nm
    simplify (DN _ nm)         = simplify nm
    simplify x                 = ([], x)

0 nct_corr_eq : nameConformsTo `{A.B.c} `{A.B.c} = True;  nct_corr_eq = Refl
0 nct_corr_le : nameConformsTo `{B.c}   `{A.B.c} = True;  nct_corr_le = Refl
0 nct_corr_ge : nameConformsTo `{A.B.c} `{B.c}   = False; nct_corr_ge = Refl

-- simple syntactic search of a `IVar`, disregarding shadowing or whatever
export
allVarNames' : TTImp -> SortedSet Name
allVarNames' = runConst . mapATTImp' f where
  f : TTImp -> Const (SortedSet Name) TTImp -> Const (SortedSet Name) TTImp
  f (IVar _ n) = const $ MkConst $ singleton n
  f _          = id

-- Same as `allVarNames'`, but returning `List`
export
allVarNames : TTImp -> List Name
allVarNames = SortedSet.toList . allVarNames'

public export
0 ArgDeps : Nat -> Type
ArgDeps n = DVect n $ SortedSet . Fin . Fin.finToNat

export
argDeps : (args : List Arg) -> ArgDeps args.length
argDeps args = do
  let nameToIndices = SortedMap.fromList $ mapI args $ \i, arg => (argName arg, SortedSet.singleton i)
  let args = Vect.fromList args <&> \arg => allVarNames arg.type |> map (fromMaybe empty . lookup' nameToIndices)
  flip upmapI args $ \i, deps => flip concatMap deps $ \candidates =>
    maybe empty singleton $ last' $ mapMaybe tryToFit $ SortedSet.toList candidates

public export
isVar : TTImp -> Bool
isVar $ IVar {} = True
isVar _         = False

namespace UpToRenaming

  mutual

    compWithSubst : (subst : List $ These Name Name) => (from, to : Maybe Name) -> TTImp -> TTImp -> Bool
    compWithSubst (Just n) (Just n') e e' = n == n' && (e == e') @{UpToSubst} || (e == e') @{UpToSubst @{Both n n' :: subst}}
    compWithSubst (Just n) Nothing   e e' = (e == e') @{UpToSubst @{This n  :: subst}}
    compWithSubst Nothing  (Just n') e e' = (e == e') @{UpToSubst @{That n' :: subst}}
    compWithSubst Nothing  Nothing   e e' = (e == e') @{UpToSubst}

    [UpToSubst] (subst : List $ These Name Name) => Eq TTImp where
      IVar _ v == IVar _ v' = maybe (v == v') (== Both v v') $ flip find subst $ \ior => fromThis ior == Just v || fromThat ior == Just v'
      IPi _ c i n a r == IPi _ c' i' n' a' r' =
        c == c' && (assert_total $ i == i') && a == a' && (assert_total $ compWithSubst n n' r r')
      ILam _ c i n a r == ILam _ c' i' n' a' r' =
        c == c' && (assert_total $ i == i') && a == a' && (assert_total $ compWithSubst n n' r r')
      ILet _ _ c n ty val s == ILet _ _ c' n' ty' val' s' =
        c == c' && ty == ty' && val == val' && (assert_total $ compWithSubst (Just n) (Just n') s s')

      ICase _ os t ty cs == ICase _ os' t' ty' cs' =
        t == t' && (assert_total $ os == os') && ty == ty' && (assert_total $ cs == cs')
      ILocal _ ds e == ILocal _ ds' e' =
        (assert_total $ ds == ds') && e == e'
      IUpdate _ fs t == IUpdate _ fs' t' =
        (assert_total $ fs == fs') && t == t'

      IApp _ f x == IApp _ f' x' = f == f' && x == x'
      INamedApp _ f n x == INamedApp _ f' n' x' =
        f == f' && n == n' && x == x'
      IAutoApp _ f x == IAutoApp _ f' x' = f == f' && x == x'
      IWithApp _ f x == IWithApp _ f' x' = f == f' && x == x'

      ISearch _ n == ISearch _ n' = n == n'
      IAlternative _ t as == IAlternative _ t' as' =
        (assert_total $ t == t') && (assert_total $ as == as')
      IRewrite _ p q == IRewrite _ p' q' =
        p == p' && q == q'

      IBindHere _ m t == IBindHere _ m' t' =
        m == m' && t == t'
      IBindVar _ s == IBindVar _ s' = s == s'
      IAs _ _ u n t == IAs _ _ u' n' t' =
        u == u' && n == n' && t == t'
      IMustUnify _ r t == IMustUnify _ r' t' =
        r == r' && t == t'

      IDelayed _ r t == IDelayed _ r' t' = r == r' && t == t'
      IDelay _ t == IDelay _ t' = t == t'
      IForce _ t == IForce _ t' = t == t'

      IQuote _ tm == IQuote _ tm' = tm == tm'
      IQuoteName _ n == IQuoteName _ n' = n == n'
      IQuoteDecl _ ds == IQuoteDecl _ ds' = assert_total $ ds == ds'
      IUnquote _ tm == IUnquote _ tm' = tm == tm'

      IPrimVal _ c == IPrimVal _ c' = c == c'
      IType _ == IType _ = True
      IHole _ s == IHole _ s' = True -- Holes are anyway unique and does not matter what the names are.

      Implicit _ b == Implicit _ b' = b == b'
      IWithUnambigNames _ ns t == IWithUnambigNames _ ns' t' =
        map snd ns == map snd ns' && t == t'

      _ == _ = False

  export
  [UpToRenaming] Eq TTImp where
    x == y = (x == y) @{UpToSubst @{empty}}

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

||| Returns a name by the generator's type
|||
||| Say, for the `Fuel -> Gen em (n ** Fin n)` it returns name of `Data.Fin.Fin`
export
genTypeName : (0 _ : Type) -> Elab Name
genTypeName g = do
  genTy <- quote g
  let (_, genTy) = unPi genTy
  let (lhs, args) = unAppAny genTy
  let IVar _ lhsName = lhs
    | _ => failAt (getFC lhs) "Generator or generator function expected"
  let True = lhsName `nameConformsTo` `{Test.DepTyCheck.Gen.Gen}
    | _ => failAt (getFC lhs) "Return type must be a generator of some type"
  let [_, genTy] = args
    | _ => failAt (getFC lhs) "Wrong number of type arguments of a generator"
  let (_, genTy) = unDPair $ getExpr genTy
  let (IVar _ genTy, _) = unApp genTy
    | (genTy, _) => failAt (getFC genTy) "Expected a type name"
  pure genTy

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
lookupByCon @{tyi} = concatMap @{Deep} lookupByType . SortedSet.toList . concatMap allVarNames' . conSubexprs . snd <=< lookup' tyi.cons

typeByCon : NamesInfoInTypes => Con -> Maybe TypeInfo
typeByCon @{tyi} = map fst . lookup' tyi.cons . name

export
lookupType : NamesInfoInTypes => Name -> Maybe TypeInfo
lookupType @{tyi} = lookup' tyi.types

export
lookupCon : NamesInfoInTypes => Name -> Maybe Con
lookupCon @{tyi} n = snd <$> lookup n tyi.cons
                 <|> typeCon <$> lookup n tyi.types

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
                       let [resolved] = SortedSet.toList resolvedAlts
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
    let new = if contains curr visited then [] else maybe [] SortedSet.toList $ lookupByType curr
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
getNamesInfoInTypes ty = go neutral [ty]
  where

    subexprs : TypeInfo -> List TTImp
    subexprs ty = map type ty.args ++ (ty.cons >>= conSubexprs)

    go : NamesInfoInTypes -> List TypeInfo -> m NamesInfoInTypes
    go tyi []         = pure tyi
    go tyi (ti::rest) = do
      ti <- normaliseCons ti
      let subes = concatMap allVarNames' $ subexprs ti
      new <- map join $ for (SortedSet.toList subes) $ \n =>
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
  varsSecondOrder <- map concat $ Prelude.for varsFirstOrder $ \n => do
                       ns <- getType n
                       pure $ SortedSet.insert n $ flip concatMap ns $ \(n', ty) => insert n' $ allVarNames' ty
  tys <- map (mapMaybe id) $ for (SortedSet.toList varsSecondOrder) $ catch . getInfo'
  concat <$> Prelude.for tys getNamesInfoInTypes

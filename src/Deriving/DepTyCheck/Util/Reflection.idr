||| `Language.Reflection`-related utilities
module Deriving.DepTyCheck.Util.Reflection

import public Control.Applicative.Const

import public Data.Alternative
import public Data.Cozippable

import public Data.Either
import public Data.Fin.Lists
import public Data.Fin.ToFin
import public Data.Fuel
import public Data.Nat1
import public Data.List.Lazy
import public Data.List.Elem
import public Data.List.Extra
import public Data.SortedMap.Extra
import public Data.These
import public Data.Vect.Dependent
import public Data.Vect.Extra

import public Data.SortedMap
import public Data.SortedMap.Dependent
import public Data.SortedSet

import public Decidable.Equality
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
%hide Text.PrettyPrint.Bernardy.Core.Doc.(>>=)

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

export
SingleLogPosition TypeInfo where
  logPosition ti = "\{show $ extractTargetTyExpr ti}"

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
  let args = comergeWith (\pre => {name := pre.name}) args args'
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

-- Apply syntactically, optimise if LHS is `ILam`.
-- This implementation does not take shadowing into account.
-- Also, currently, the type of lambda argument is not used in the final expression, this can break typechecking in complex cases.
public export
applySyn : TTImp -> TTImp -> TTImp
applySyn (ILam _ _ _ Nothing  _ lamExpr) _ = lamExpr
applySyn (ILam _ _ _ (Just n) _ lamExpr) rhs = mapTTImp (\case orig@(IVar _ n') => if n == n' then rhs else orig; e => e) lamExpr
applySyn lhs rhs = lhs `app` rhs

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

export
reflectNat1 : Nat1 -> TTImp
reflectNat1 $ FromNat 1 = liftWeight1
reflectNat1 $ FromNat n = `(fromInteger ~(primVal $ BI $ cast n))

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
allVarNames = Prelude.toList . allVarNames'

public export
0 ArgDeps : Nat -> Type
ArgDeps n = DVect n $ SortedSet . Fin . Fin.finToNat

export
argDeps : (args : List Arg) -> ArgDeps args.length
argDeps args = do
  let nameToIndices = SortedMap.fromList $ mapI args $ \i, arg => (argName arg, SortedSet.singleton i)
  let args = Vect.fromList args <&> \arg => allVarNames arg.type |> map (fromMaybe empty . lookup' nameToIndices)
  flip upmapI args $ \i, deps => flip concatMap deps $ \candidates =>
    maybe empty singleton $ last' $ mapMaybe tryToFit $ Prelude.toList candidates

export
dependees : (args : List Arg) -> SortedSet $ Fin $ args.length
dependees args = do
  let nameToIndex = SortedMap.fromList $ mapI args $ \i, arg => (argName arg, i)
  let varsInTypes = concatMap (\arg => allVarNames' arg.type) args
  fromList $ mapMaybe (lookup' nameToIndex) $ Prelude.toList varsInTypes

public export
isVar : TTImp -> Bool
isVar $ IVar {} = True
isVar _         = False

getAppVar : TTImp -> Maybe Name
getAppVar e = case fst $ unAppAny e of IVar _ n => Just n; _ => Nothing

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

--------------------------------------
--- Compile-time constructors info ---
--------------------------------------

--- Constructor argument with nice literals ---

public export
record ConArg (0 con : Con) where
  constructor MkConArg
  conArgIdx : Fin con.args.length

namespace ConArg

  public export
  fromInteger : (x : Integer) -> So (integerLessThanNat x con.args.length) => ConArg con
  fromInteger x = MkConArg $ fromInteger x

  elemToFin : Elem e xs -> Fin xs.length
  elemToFin Here      = FZ
  elemToFin (There x) = FS $ elemToFin x

  public export
  fromName : (n : Name) -> Elem (Just n) (map Arg.name con.args) => ConArg con
  fromName _ @{e} = MkConArg $ rewrite sym $ lengthMap con.args in elemToFin e

  -- this function is not exported because it breaks type inference in polymorphic higher-kinded case,
  -- but we still leave this a) in a hope that type inference woukd be improved; b) to make sure we still can implement it.
  --public export
  fromString : (n : String) -> Elem (Just $ fromString n) (map Arg.name con.args) => ConArg con
  fromString n = fromName $ fromString n

--- Getting full names of a data constructor ---

dataCon : Name -> Elab Name
dataCon n = do
  [n] <- mapMaybe id <$> (traverse isAccessibleDataCon =<< getInfo n)
    | [] => fail "Not found data constructor `\{n}`"
    | ns => fail "Ambiguous data constructors: \{joinBy ", " $ show <$> ns}"
  pure n

  where
    isAccessibleDataCon : (Name, NameInfo) -> Elab $ Maybe Name
    isAccessibleDataCon (n, MkNameInfo $ DataCon {}) = (catch (check {expected=()} `(let x = ~(var n) in ())) $> n) @{Compose}
    isAccessibleDataCon _                            = pure Nothing

export %macro (.dataCon) : Name -> Elab Name; (.dataCon) = dataCon

--- Information about constructors ---

public export
record IsConstructor (0 n : Name) where
  constructor ItIsCon
  typeInfo : TypeInfo
  conInfo  : Con

namespace IsConstructor
  export
  data GenuineProof : IsConstructor n -> Type where
    ItIsGenuine : GenuineProof iscn

export %macro
itIsConstructor : {n : Name} -> Elab (con : IsConstructor n ** GenuineProof con)
itIsConstructor = do
  cn <- dataCon n
  let True = n == cn
    | False => fail "Name `\{show n}` is not a full name, use either `\{show cn}` or macro `.dataCon`"
  con <- getCon cn
  let (IVar _ ty, _) = unAppAny con.type
    | (lhs, _) => fail "Can't get type name: \{show lhs}"
  ty <- getInfo' ty
  pure (ItIsCon ty con ** ItIsGenuine)

-------------------------------
--- Tuning of probabilities ---
-------------------------------

public export
interface ProbabilityTuning (0 n : Name) where
  0 isConstructor : (con : IsConstructor n ** GenuineProof con)
  tuneWeight : Nat1 -> Nat1

----------------------------------
--- Constructors recursiveness ---
----------------------------------

||| Weight info of recursive constructors
public export
data RecWeightInfo : Type where
  SpendingFuel : ((leftFuelVarName : String) -> TTImp) -> RecWeightInfo
  StructurallyDecreasing : (decrTy : Name) -> (wExpr : TTImp) -> RecWeightInfo

public export
record ConWeightInfo where
  constructor MkConWeightInfo
  ||| Either a constant (for non-recursive) or a function returning weight info (for recursive)
  weight : Either Nat1 RecWeightInfo

public export
weightExpr : ConWeightInfo -> Either TTImp ((leftFuelVarName : String) -> TTImp)
weightExpr $ MkConWeightInfo $ Left n = Left $ reflectNat1 n
weightExpr $ MkConWeightInfo $ Right $ StructurallyDecreasing {wExpr, _} = Left wExpr
weightExpr $ MkConWeightInfo $ Right $ SpendingFuel e = Right e

export
record ConsRecs where
  constructor MkConsRecs
  ||| Map from a type name to a list of its constructors with their weight info
  -- TODO to change `SortedSet Nat` to `GenSignature`, but this requires moving all this to a module that can import `*/Derive.idr`
  conWeights : SortedMap Name $ List (Con, (givenTyArgs : SortedSet Nat) -> ConWeightInfo)
  ||| Derive a function for weighting weightable type, if given type is weightable
  deriveWeightingFun : (weightableType : Name) -> Maybe (Decl, Decl)

-- This is a workaround of some bad and not yet understood behaviour, leading to both compile- and runtime errors
removeNamedApps, workaroundFromNat : TTImp -> TTImp
removeNamedApps = mapTTImp $ \case INamedApp _ lhs _ _ => lhs; e => e
workaroundFromNat = mapTTImp $ \e => case fst $ unAppAny e of IVar _ `{Data.Nat1.FromNat} => removeNamedApps e; _ => e

weightFunName : Name -> Name
weightFunName n = fromString "weight^\{show n}"

-- this is a workarond for Idris compiler bug #2983
export
interimNamesWrapper : Name -> String
interimNamesWrapper n = "inter^<\{show n}>"

export
getConsRecs : Elaboration m => (niit : NamesInfoInTypes) => m ConsRecs
getConsRecs = do
  consRecs <- for niit.types $ \targetType => logBounds {level=DetailedTrace} "consRec" [targetType] $ do
    crsForTy <- for targetType.cons $ \con => do
      let rec = isRecursive {containingType=Just targetType} con
      tuneImpl <- search $ ProbabilityTuning con.name
      w : Either Nat1 (TTImp -> TTImp, Maybe $ SortedSet $ Fin con.args.length) <- case rec of
        --             ^^^^^^^^^^^^^^  ^^^^^   ^^^^^^^^^^^^^^^ <- set of directly recursive constructor arguments
        --                   |           \-- `Just` in this `Maybe` means that this constructor only contains direct recursion (not mutual one)
        --                    \------ Modifier of the standard weight expression
        False => pure $ Left $ maybe one (\impl => tuneWeight @{impl} one) tuneImpl
        True  => Right <$> do
          fuelWeightExpr <- case tuneImpl of
            Nothing   => pure id
            Just impl => quote (tuneWeight @{impl}) <&> \wm, expr => workaroundFromNat $ wm `applySyn` expr
          let directlyRec = filter (not . null) $ map (fromList . mapMaybe id) $ for con.args.withIdx $ \(idx, arg) => do
            case (== targetType.name) <$> getAppVar arg.type of
              Just True => Just $ Just idx
              _         => if hasNameInsideDeep targetType.name arg.type then Nothing else Just Nothing
          let logDirectRec = \ars => logPoint {level=DetailedTrace} "consRec" [targetType, con]
                               "Constructor is detected as a directly recursive with recursive args \{show $ finToNat <$> ars.asList}"
          maybe (pure ()) logDirectRec directlyRec
          pure (fuelWeightExpr, directlyRec)
      pure (con ** w)
    -- determine if this type is a nat-or-list-like data, i.e. one which we can measure for the probability
    let weightable = flip all crsForTy $ \case (_ ** Right (_, Nothing)) => False; _ => True
    pure (whenT weightable targetType.name, crsForTy)
  let 0 _ : SortedMap Name (Maybe Name, List (con : Con ** Either Nat1 (TTImp -> TTImp, Maybe $ SortedSet $ Fin con.args.length))) := consRecs

  let weightableTyArgs : (ars : List Arg) -> SortedMap Nat (Name, Name) -- <- a map from Fin ars.length to a weightable type name and its argument name
      weightableTyArgs ars = fromList $ flip List.mapMaybe ars.withIdx $ \(idx, ar) =>
                               getAppVar ar.type >>= lookup' consRecs <&> fst >>= \tyN => [| (finToNat idx,,) tyN ar.name |]

  let finalConsRecs = mapWithKey' consRecs $ \tyName, (_, cons) => do
    let wTyArgs = maybe SortedMap.empty .| weightableTyArgs . args .| lookupType tyName
    cons <&> \(con ** e) => (con,) $ \givenTyArgs => MkConWeightInfo $ e <&> \(wMod, directRecConArgs) => do
      -- default behaviour, spend fuel, weight proportional to fuel
      fromMaybe (SpendingFuel $ wMod . app `(Deriving.DepTyCheck.Util.Reflection.leftDepth) . varStr) $ do
      -- fail-fast if no direct args in this constructor
      guard $ isJust directRecConArgs
      -- work only with given args
      let wTyArgs = wTyArgs `intersectionMap` givenTyArgs
      -- fail-fast if no given weightable args
      guard $ not $ null wTyArgs
      -- If for any weightable type argument (in `wTyArgs`) there exists a directly recursive constructor arg (in `directRecConArgs`) that has
      -- this type argument strictly decreasing, we consider this constructor to be non-fuel-spending.
      let conRetTyArgs = snd $ unAppAny con.type
      let conArgs = con.args
      let conArgNames = SortedSet.fromList $ mapMaybe name conArgs
      (decrTy, weightExpr) <- foldAlt' wTyArgs.asList $ \(wTyArg, weightTyName, weightArgName) => map (weightTyName,) $ do
        conRetTyArg <- getExpr <$> getAt wTyArg conRetTyArgs
        guard $ isJust $ lookupCon =<< getAppVar conRetTyArg
        let freeNamesLessThanOrig = allVarNames' conRetTyArg `intersection` conArgNames
        foldAlt' conArgs $ \conArg => case unAppAny conArg.type of (conArgTy, conArgArgs) => whenTs (getAppVar conArgTy == Just tyName) $ do
          getAt wTyArg conArgArgs >>= getAppVar . getExpr >>= \arg => whenT .| contains arg freeNamesLessThanOrig .|
            var (weightFunName weightTyName) .$ varStr (interimNamesWrapper weightArgName)
      pure $ StructurallyDecreasing decrTy $ wMod weightExpr

  let deriveWeightingFun = \tyName => Nothing -- TODO to implement

  pure $ MkConsRecs finalConsRecs deriveWeightingFun

export
lookupConsWithWeight : ConsRecs => TypeInfo -> Maybe $ List (Con, (givenTyArgs : SortedSet Nat) -> ConWeightInfo)
lookupConsWithWeight @{crs} = lookup' crs.conWeights . name

--------------------------------
--- Permutation of arguments ---
--------------------------------

export
orderIndices : Ord a => (xs : List a) -> Vect xs.length $ Fin xs.length
orderIndices [] = []
orderIndices xs@(_::_) = do
  let idxMap = SortedMap.fromList $ mapI (sort xs) $ flip $ rewrite sortedPreservesLength xs in (,)
  fromMaybe FZ . lookup' idxMap <$> xs.asVect
  --        ^^ - must never happen, if `Ord` is an order mathematically
  where
    sortedPreservesLength : (xs : List a) -> length (sort xs) = xs.length
    sortedPreservesLength xs = believe_me $ Refl {x=Z} -- in the sake of honesty, we need to prove this

export
reorder : (perm : Vect n $ Fin n) -> Vect n a -> Vect n a
reorder perm orig = perm <&> flip index orig

export
reorder' : (xs : List a) -> (perm : Vect xs.length $ Fin xs.length) -> (ys : List a ** ys.length = xs.length)
reorder' orig perm = do
  let xs = reorder perm orig.asVect
  (toList xs ** toListLength xs)
  where
    toList : Vect n a -> List a
    toList []      = []
    toList (x::xs) = x :: toList xs

    toListLength : (xs : Vect n a) -> length (toList xs) = n
    toListLength []      = Refl
    toListLength (x::xs) = rewrite toListLength xs in Refl

export
reorder'' : Maybe (n ** Vect n $ Fin n) -> List TTImp -> Maybe $ List TTImp
reorder'' Nothing xs = pure xs
reorder'' (Just (n ** perm)) xs = do
  let Yes prf = decEq (length xs) n | No _ => Nothing
  Just $ fst $ reorder' xs $ rewrite prf in perm

||| Produces expression returning a mkdpair in a different order, if needed
|||
||| Direct means that given expression which returns acending order, result is permutated; non-direct means vice versa.
export
reorderGend : (direct : Bool) -> {n : _} -> (perm : Vect n $ Fin n) -> TTImp -> TTImp
reorderGend direct perm e = do
  let perm = toList perm
  let all = allFins _
  let False = perm == all | True => e
  let (lhs, rhs) : (_, _) := if direct then (all, perm) else (perm, all)
  let lhs = simpleMkdpair True lhs
  let rhs = simpleMkdpair False rhs
  let lamName : Name := "^lam_arg^"
  `(Prelude.(<&>)) .$ e .$ lam (lambdaArg lamName) (iCase (var lamName) implicitFalse $ pure $ patClause lhs rhs)
  where
    v : (bind : Bool) -> String -> TTImp
    v bind = if bind then bindVar else varStr
    simpleMkdpair : (bind : Bool) -> List (Fin n) -> TTImp
    simpleMkdpair bind = foldr (app . (app `(Builtin.DPair.MkDPair)) . v bind . ("^a" ++) . show) (v bind "^res^")

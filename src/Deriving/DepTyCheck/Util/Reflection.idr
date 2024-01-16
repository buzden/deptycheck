||| `Language.Reflection`-related utilities
module Deriving.DepTyCheck.Util.Reflection

import public Data.Fin
import public Data.Fuel
import public Data.Nat.Pos
import public Data.List.Lazy
import public Data.These
import public Data.Vect.Dependent
import public Data.Vect.Extra

import public Data.SortedMap
import public Data.SortedMap.Dependent
import public Data.SortedSet

import public Deriving.DepTyCheck.Util.Alternative
import public Deriving.DepTyCheck.Util.Collections
import public Deriving.DepTyCheck.Util.Fin
import public Deriving.DepTyCheck.Util.Logging
import public Deriving.DepTyCheck.Util.Syntax

import public Language.Reflection.TTImp
import public Language.Reflection.Types
import public Language.Reflection.Pretty

%default total

-----------------------
--- Pretty-printing ---
-----------------------

export
Interpolation TTImp where
  interpolate expr = show $ assert_total $ pretty {ann=Unit} expr

export
Interpolation Decl where
  interpolate decl = show $ assert_total $ pretty {ann=Unit} decl

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

-- This is a workaround to not to change `elab-util`'s `gitInfo'`
export
normaliseCon : Elaboration m => Con -> m Con
normaliseCon $ MkCon n args ty = do
  let whole = piAll ty $ args <&> {name $= Just}
  whole <- normaliseAsType whole
  (args', ty) <- unPiNamed whole
  -- `quote` may corrupt names, workaround it:
  let args = args `zip` args' <&> \(pre, normd) => {name := argName pre} normd
  pure $ MkCon n args ty

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
unDPair : TTImp -> (List (Arg False), TTImp)
unDPair (IApp _ (IApp _ (IVar _ `{Builtin.DPair.DPair}) typ) (ILam _ cnt piInfo mbname _ lamTy)) =
    mapFst (MkArg cnt piInfo mbname typ ::) $ unDPair lamTy
unDPair expr = ([], expr)

public export
unDPairUnAlt : TTImp -> Maybe (List (Arg False), TTImp)
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
appArg : NamedArg -> TTImp -> AnyApp
appArg (MkArg {piInfo=ExplicitArg, _})         expr = PosApp expr
appArg (MkArg {piInfo=ImplicitArg, name, _})   expr = NamedApp name expr
appArg (MkArg {piInfo=DefImplicit _, name, _}) expr = NamedApp name expr
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

public export
reAppAny : TTImp -> List AnyApp -> TTImp
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
liftWeight1 = `(Data.Nat.Pos.one)

export
labelGen : (desc : String) -> TTImp -> TTImp
labelGen desc expr = `(Test.DepTyCheck.Gen.label (fromString ~(primVal $ Str desc)) ~expr)

export
callOneOf : (desc : String) -> List TTImp -> TTImp
callOneOf desc [v]      = labelGen desc v
callOneOf desc variants = labelGen desc $ `(Test.DepTyCheck.Gen.oneOf {em=MaybeEmpty}) .$ liftList variants

-- List of weights and subgenerators
export
callFrequency : (desc : String) -> List (TTImp, TTImp) -> TTImp
callFrequency _    [(_, v)] = v
callFrequency desc variants = labelGen desc $ var `{Test.DepTyCheck.Gen.frequency} .$
                                liftList (variants <&> \(freq, subgen) => var `{Builtin.MkPair} .$ freq .$ subgen)

-- TODO to think of better placement for this function; this anyway is intended to be called from the derived code.
public export
leftDepth : Fuel -> PosNat
leftDepth = go 1 where
  go : PosNat -> Fuel -> PosNat
  go n Dry      = n
  go n (More x) = go (succ n) x

export
isSimpleBindVar : TTImp -> Bool
isSimpleBindVar $ IBindVar {} = True
isSimpleBindVar _             = False

export
callCon : (con : Con) -> Vect con.args.length TTImp -> TTImp
callCon con = reAppAny (var con.name) . toList . mapWithPos (appArg . index' con.args)

export
outmostFuelArg : Name
outmostFuelArg = UN $ Basic "^outmost-fuel^" -- I'm using a name containing chars that cannot be present in the code parsed from the Idris frontend

---------------------------------------
--- Working around primitive values ---
---------------------------------------

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

----------------------------------------------
--- Analyzing dependently typed signatures ---
----------------------------------------------

export
doesTypecheckAs : Elaboration m => (0 expected : Type) -> TTImp -> m Bool
doesTypecheckAs expected expr = try .| check {expected} expr $> True .| pure False

export
argDeps : Elaboration m => (args : List NamedArg) -> m $ DVect args.length $ SortedSet . Fin . Fin.finToNat
argDeps args = do
  ignore $ check {expected=Type} $ fullSig defaultRet -- we can't return trustful result if given arguments do not form a nice Pi type
  concatMap depsOfOne range

  where

  %unbound_implicits off -- this is a workaround of https://github.com/idris-lang/Idris2/issues/2040

  filteredArgs : (excluded : SortedSet $ Fin args.length) -> List NamedArg
  filteredArgs excluded = filterI' args $ \idx, _ => not $ contains idx excluded

  partialSig : (retTy : TTImp) -> (excluded : SortedSet $ Fin args.length) -> TTImp
  partialSig retTy = piAll retTy . map {name $= Just, piInfo := ExplicitArg} . filteredArgs

  partialApp : (appliee : Name) -> (excluded : SortedSet $ Fin args.length) -> TTImp
  partialApp n = appNames n . map name . filteredArgs

  fullSig : (retTy : TTImp) -> TTImp
  fullSig t = partialSig t empty

  fullApp : (appliee : Name) -> TTImp
  fullApp n = partialApp n empty

  defaultRet : TTImp
  defaultRet = `(Builtin.Unit)

  -- This is for check that *meaning* of types are preversed after excluding some of arguments
  --
  -- Example:
  --   Consider that `args` form the following: `(n : Nat) -> (a : Type) -> (v : Vect n a) -> (x : Nat) -> ...`
  --   Consider we have `excluded` set containing only index 3 (the `x : Nat` argument).
  --   For this case this function would return the following type:
  --   ```
  --     (full : (n : Nat) -> (a : Type) -> (v : Vect n a) -> (x : Nat) -> Unit) ->
  --     (part : (n : Nat) -> (a : Type) -> (v : Vect n a) -> Unit) ->
  --     (n : Nat) -> (a : Type) -> (v : Vect n a) -> (x : Nat) ->
  --     full n a v x = part n a v
  --   ```
  --   As soon as this expression typechecks as `Type`, we are confident that
  --   corresponding parameters of the full and the partial signatures are compatible, i.e.
  --   removing of the parameters from `excluded` set does not change left types too much.
  preservationCheckSig : (excluded : SortedSet $ Fin args.length) -> TTImp
  preservationCheckSig excluded =
    pi (MkArg MW ExplicitArg .| Just full .| fullSig defaultRet) $
    pi (MkArg MW ExplicitArg .| Just part .| partialSig defaultRet excluded) $
    fullSig $
    `(Builtin.Equal) .$ fullApp full .$ partialApp part excluded
    where
      full, part : Name
      full = MN "full" 1
      part = MN "part" 1

  checkExcluded : (excluded : SortedSet $ Fin args.length) -> m Bool
  checkExcluded excluded = doesTypecheckAs Type (partialSig defaultRet excluded)
                        && doesTypecheckAs Type (preservationCheckSig excluded)

  -- Returns a set of indices of all arguments that do depend on the given
  depsOfOne' : (idx : Fin args.length) -> m $ SortedSet $ Fin args.length
  depsOfOne' idx = do
    let cands = allGreaterThan idx
    findMinExclude cands $ fromList cands

    where
      -- tries to add candidates one by one, and leave them if typechecks without the current `idx`
      findMinExclude : (left : List $ Fin args.length) -> (currExcl : SortedSet $ Fin args.length) -> m $ SortedSet $ Fin args.length
      findMinExclude [] excl = pure excl
      findMinExclude (x::xs) prevExcl = do
        let currExcl = delete x prevExcl
        findMinExclude xs $ if !(checkExcluded $ insert idx currExcl) then currExcl else prevExcl

  depsOfOne : Fin args.length -> m $ DVect args.length $ SortedSet . Fin . Fin.finToNat
  depsOfOne idx = do
    whoDependsOnIdx <- depsOfOne' idx
    sequence $ tabulateI $ \i =>
      if contains i whoDependsOnIdx
      then do
        let Just dep = tryToFit idx
          | Nothing => fail "INTERNAL ERROR: unable to fit fins during dependency calculation"
        pure $ singleton dep
      else pure empty

  %unbound_implicits on -- this is a workaround of https://github.com/idris-lang/Idris2/issues/2039

  Semigroup a => Applicative f => Semigroup (f a) where
    a <+> b = [| a <+> b |]

  Monoid a => Applicative f => Monoid (f a) where
    neutral = pure neutral

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
    let tyApplied = reAppAny (var ti.name) $ ti.args <&> \arg => appArg arg $ var $ Arg.name arg
    let sig = foldr
                (pi . {count := M0, piInfo := ImplicitArg, name $= Just})
                `(~tyApplied -> ~retTy)
                ti.args
    private' funName sig
  let body = do
    let matchCon = \con => reAppAny (var con.name) $ con.args <&> flip appArg implicitTrue
    def funName $ ti.cons <&> \con =>
      patClause (var funName .$ matchCon con) $ matcher con
  [claim, body]

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
allVarNames : TTImp -> LazyList Name
allVarNames expr = ttimp expr where
  mutual

    ttimp : TTImp -> LazyList Name
    ttimp $ IVar _ n                        = [n]
    ttimp $ IPi _ _ z _ argTy retTy         = ttimp argTy ++ ttimp retTy ++ piInfo z
    ttimp $ ILam _ _ z _ argTy lamTy        = ttimp argTy ++ ttimp lamTy ++ piInfo z
    ttimp $ ILet _ _ _ _ nTy nVal sc        = ttimp nTy ++ ttimp nVal ++ ttimp sc -- should we check `nTy` here?
    ttimp $ ICase _ _ _ ty xs               = ttimp ty ++ assert_total (foldMap clause xs)
    ttimp $ ILocal _ xs y                   = assert_total (foldMap decl xs) ++ ttimp y
    ttimp $ IUpdate _ xs y                  = assert_total (foldMap fieldUpdate xs) ++ ttimp y
    ttimp $ IApp _ y z                      = ttimp y ++ ttimp z
    ttimp $ INamedApp _ y _ w               = ttimp y ++ ttimp w
    ttimp $ IAutoApp _ y z                  = ttimp y ++ ttimp z
    ttimp $ IWithApp _ y z                  = ttimp y ++ ttimp z
    ttimp $ ISearch _ _                     = []
    ttimp $ IAlternative _ y xs             = altType y ++ assert_total (foldMap ttimp xs)
    ttimp $ IRewrite _ y z                  = ttimp y ++ ttimp z
    ttimp $ IBindHere _ _ z                 = ttimp z
    ttimp $ IBindVar _ _                    = []
    ttimp $ IAs _ _ _ _ w                   = ttimp w
    ttimp $ IMustUnify _ _ z                = ttimp z
    ttimp $ IDelayed _ _ z                  = ttimp z
    ttimp $ IDelay _ y                      = ttimp y
    ttimp $ IForce _ y                      = ttimp y
    ttimp $ IQuote _ y                      = ttimp y
    ttimp $ IQuoteName _ _                  = []
    ttimp $ IQuoteDecl _ xs                 = assert_total $ foldMap decl xs
    ttimp $ IUnquote _ y                    = ttimp y
    ttimp $ IPrimVal _ _                    = []
    ttimp $ IType _                         = []
    ttimp $ IHole _ _                       = []
    ttimp $ Implicit _ _                    = []
    ttimp $ IWithUnambigNames _ _ y         = ttimp y

    altType : AltType -> LazyList Name
    altType FirstSuccess      = []
    altType Unique            = []
    altType (UniqueDefault x) = ttimp x

    lncpt : List (Name, Count, PiInfo TTImp, TTImp) -> LazyList Name
    lncpt = foldMap (\(_, _, pii, tt) => piInfo pii ++ ttimp tt)

    ity : ITy -> LazyList Name
    ity $ MkTy _ _ _ ty = ttimp ty

    decl : Decl -> LazyList Name
    decl $ IClaim _ _ _ _ t                         = ity t
    decl $ IData _ _ _ z                            = data_ z
    decl $ IDef _ _ xs                              = foldMap clause xs
    decl $ IParameters _ xs ys                      = lncpt xs ++ assert_total (foldMap decl ys)
    decl $ IRecord _ _ _ _ $ MkRecord _ _ ps _ _ fs = lncpt ps ++ foldMap (\(MkIField _ _ pii _ tt) => piInfo pii ++ ttimp tt) fs
    decl $ INamespace _ _ xs                        = assert_total $ foldMap decl xs
    decl $ ITransform _ _ z w                       = ttimp z ++ ttimp w
    decl $ IRunElabDecl _ y                         = ttimp y
    decl $ ILog _                                   = []
    decl $ IBuiltin _ _ _                           = []

    data_ : Data -> LazyList Name
    data_ $ MkData x n tycon _ datacons = maybe [] ttimp tycon ++ foldMap ity datacons
    data_ $ MkLater x n tycon           = ttimp tycon

    fieldUpdate : IFieldUpdate -> LazyList Name
    fieldUpdate $ ISetField    _ x = ttimp x
    fieldUpdate $ ISetFieldApp _ x = ttimp x

    clause : Clause -> LazyList Name
    clause $ PatClause _ lhs rhs            = ttimp lhs ++ ttimp rhs
    clause $ WithClause _ lhs _ wval _ _ xs = ttimp lhs ++ ttimp wval ++ assert_total (foldMap clause xs)
    clause $ ImpossibleClause _ lhs         = ttimp lhs

    piInfo : PiInfo TTImp -> LazyList Name
    piInfo ImplicitArg     = []
    piInfo ExplicitArg     = []
    piInfo AutoImplicit    = []
    piInfo (DefImplicit x) = ttimp x

export
record NamesInfoInTypes where
  constructor Names
  names : SortedMap Name $ List TTImp

export
hasNameInsideDeep : NamesInfoInTypes => Name -> TTImp -> Bool
hasNameInsideDeep @{tyi} nm expr = hasInside empty [expr] where

  hasInside : (visited : SortedSet Name) -> (toLook : List TTImp) -> Bool
  hasInside visited []           = False
  hasInside visited (curr::rest) = do
    let vs = toList $ allVarNames curr
    let False = any (== nm) vs
      | True => True
    let nonVisited = filter (not . flip contains visited) vs
    let new = nonVisited >>= \n => fromMaybe [] $ lookup n tyi.names
    -- visited is limited and either growing or `new` is empty, thus `toLook` is strictly less
    assert_total $ hasInside (visited `union` fromList nonVisited) (new ++ rest)

export
getNamesInfoInTypes : Elaboration m => TypeInfo -> m NamesInfoInTypes
getNamesInfoInTypes ty = Names <$> go empty [ty]
  where

    subexprs : TypeInfo -> List TTImp
    subexprs ty = map type ty.args ++ (ty.cons >>= \con => con.type :: map type con.args)

    go : SortedMap Name (List TTImp) -> List TypeInfo -> m $ SortedMap Name (List TTImp)
    go tyi []         = pure tyi
    go tyi (ti::rest) = do
      let subes = subexprs ti
      new <- map join $ for subes $ map (mapMaybe id) . traverse (catch . getInfo') . filter (isNothing . flip lookup tyi) . allVarNames
      assert_total $ go (insert ti.name subes tyi) (new ++ rest)

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
    let (c::left) = filter (not . isJust . flip lookup curr . name) left
      | [] => pure curr
    let next = insert c.name c curr
    args <- atRig M0 $ join <$> for c.args typesOfArg
    cons <- join <$> for c.cons typesOfCon
    assert_total $ go (args ++ cons ++ left) next
    where
      atRig : Count -> m (List a) -> m (List a)
      atRig rig act = if rig >= minimalRig then act else pure []

      typesOfExpr : TTImp -> m $ List TypeInfo
      typesOfExpr expr = map (mapMaybe id) $ for (allVarNames expr) $ catch . getInfo'

      typesOfArg : NamedArg -> m $ List TypeInfo
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

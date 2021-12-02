||| `Language.Reflection`-related utilities
module Test.DepTyCheck.Gen.Auto.Util.Reflection

import public Data.Fin
import public Data.List.Lazy
import public Data.Vect.Dependent
import public Data.Vect.Extra

import public Data.SortedMap
import public Data.SortedMap.Dependent
import public Data.SortedSet

import public Language.Reflection.TTImp
import public Language.Reflection.Types

import public Test.DepTyCheck.Gen.Auto.Util.Alternative
import public Test.DepTyCheck.Gen.Auto.Util.Collections
import public Test.DepTyCheck.Gen.Auto.Util.Fin
import public Test.DepTyCheck.Gen.Auto.Util.Syntax

%default total

--------------------------------------------
--- Parsing and rebuilding `TTImp` stuff ---
--------------------------------------------

--- `DPair` type parsing and rebuilding stuff ---

public export
unDPair : TTImp -> (List (Arg False), TTImp)
unDPair (IApp _ (IApp _ (IVar _ `{Builtin.DPair.DPair}) typ) (ILam _ cnt piInfo mbname _ lamTy)) =
    mapFst (MkArg cnt piInfo mbname typ ::) $ unDPair lamTy
unDPair expr = ([], expr)

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
liftList = foldr (\l, r => `(~(l) :: ~(r))) `([])

export
callOneOf : List TTImp -> TTImp
callOneOf variants = var `{Test.DepTyCheck.Gen.oneOf'} .$ liftList variants

export
isSimpleBindVar : TTImp -> Bool
isSimpleBindVar $ IBindVar {} = True
isSimpleBindVar _             = False

export
callCon : (con : Con) -> Vect con.args.length TTImp -> TTImp
callCon con = reAppAny (var con.name) . toList . mapWithPos (appArg . index' con.args)

--- General purpose instances ---

public export
Eq Namespace where
  MkNS xs == MkNS ys = xs == ys

export
Ord Namespace where
  compare = comparing $ \(MkNS xs) => xs

public export
Eq UserName where
  Basic x    == Basic y    = x == y
  Field x    == Field y    = x == y
  Underscore == Underscore = True
  _ == _ = False

export
Ord UserName where
  compare = comparing characteristic where
    characteristic : UserName -> (Int, String)
    characteristic $ Basic x    = (0, x)
    characteristic $ Field x    = (1, x)
    characteristic $ Underscore = (2, "")

public export
Eq Name where
  UN x   == UN y   = x == y
  MN x n == MN y m = x == y && n == m
  NS s n == NS p m = s == p && n == m
  DN x n == DN y m = x == y && n == m

  Nested x n    == Nested y m    = x == y && n == m
  CaseBlock x n == CaseBlock y m = x == y && n == m
  WithBlock x n == WithBlock y m = x == y && n == m

  _ == _ = False

export
Ord Name where
  compare (DN _ x) y        = compare x y
  compare x        (DN _ y) = compare x y

  compare (NS x y) (NS z w)        = compare x z <+> compare y w
  compare (NS _ _) (UN _)          = LT
  compare (NS _ _) (MN _ _)        = LT
  compare (NS _ _) (Nested _ _)    = LT
  compare (NS _ _) (CaseBlock _ _) = LT
  compare (NS _ _) (WithBlock _ _) = LT

  compare (UN _) (NS _ _)        = GT
  compare (UN x) (UN y)          = compare x y
  compare (UN _) (MN _ _)        = LT
  compare (UN _) (Nested _ _)    = LT
  compare (UN _) (CaseBlock _ _) = LT
  compare (UN _) (WithBlock _ _) = LT

  compare (MN _ _) (NS _ _)        = GT
  compare (MN _ _) (UN _)          = GT
  compare (MN x y) (MN z w)        = compare x z <+> compare y w
  compare (MN _ _) (Nested _ _)    = LT
  compare (MN _ _) (CaseBlock _ _) = LT
  compare (MN _ _) (WithBlock _ _) = LT

  compare (Nested _ _) (NS _ _)        = GT
  compare (Nested _ _) (UN _)          = GT
  compare (Nested _ _) (MN _ _)        = GT
  compare (Nested x y) (Nested z w)    = compare x z <+> compare y w
  compare (Nested _ _) (CaseBlock _ _) = LT
  compare (Nested _ _) (WithBlock _ _) = LT

  compare (CaseBlock _ _) (NS _ _)        = GT
  compare (CaseBlock _ _) (UN _)          = GT
  compare (CaseBlock _ _) (MN _ _)        = GT
  compare (CaseBlock _ _) (Nested _ _)    = GT
  compare (CaseBlock x y) (CaseBlock z w) = compare x z <+> compare y w
  compare (CaseBlock _ _) (WithBlock _ _) = LT

  compare (WithBlock _ _) (NS _ _)        = GT
  compare (WithBlock _ _) (UN _)          = GT
  compare (WithBlock _ _) (MN _ _)        = GT
  compare (WithBlock _ _) (Nested _ _)    = GT
  compare (WithBlock _ _) (CaseBlock _ _) = GT
  compare (WithBlock x y) (WithBlock z w) = compare x z <+> compare y w

---------------------------------------
--- Working around primitive values ---
---------------------------------------

export
primTypeInfo : String -> TypeInfo
primTypeInfo s = MkTypeInfo (UN $ Basic s) [] []

export
typeInfoOfConstant : Constant -> Maybe TypeInfo
typeInfoOfConstant (I _)       = Nothing
typeInfoOfConstant (BI _)      = Nothing
typeInfoOfConstant (I8 _)      = Nothing
typeInfoOfConstant (I16 _)     = Nothing
typeInfoOfConstant (I32 _)     = Nothing
typeInfoOfConstant (I64 _)     = Nothing
typeInfoOfConstant (B8 _)      = Nothing
typeInfoOfConstant (B16 _)     = Nothing
typeInfoOfConstant (B32 _)     = Nothing
typeInfoOfConstant (B64 _)     = Nothing
typeInfoOfConstant (Str _)     = Nothing
typeInfoOfConstant (Ch _)      = Nothing
typeInfoOfConstant (Db _)      = Nothing
typeInfoOfConstant WorldVal    = Nothing
typeInfoOfConstant IntType     = Just $ primTypeInfo "Int"
typeInfoOfConstant IntegerType = Just $ primTypeInfo "Integer"
typeInfoOfConstant Int8Type    = Just $ primTypeInfo "Int8"
typeInfoOfConstant Int16Type   = Just $ primTypeInfo "Int16"
typeInfoOfConstant Int32Type   = Just $ primTypeInfo "Int32"
typeInfoOfConstant Int64Type   = Just $ primTypeInfo "Int64"
typeInfoOfConstant Bits8Type   = Just $ primTypeInfo "Bits8"
typeInfoOfConstant Bits16Type  = Just $ primTypeInfo "Bits16"
typeInfoOfConstant Bits32Type  = Just $ primTypeInfo "Bits32"
typeInfoOfConstant Bits64Type  = Just $ primTypeInfo "Bits64"
typeInfoOfConstant StringType  = Just $ primTypeInfo "String"
typeInfoOfConstant CharType    = Just $ primTypeInfo "Char"
typeInfoOfConstant DoubleType  = Just $ primTypeInfo "Double"
typeInfoOfConstant WorldType   = Nothing

-------------------------------------
--- Working around type inference ---
-------------------------------------

public export
argName : NamedArg -> Name
argName = (.name)

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
  concatMap depsOfOne $ allFins' _

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

-------------------------------------------------
--- Syntactic analysis of `TTImp` expressions ---
-------------------------------------------------

-- simple syntactic search of a `IVar`, disregarding shadowing or whatever
export
allVarNames : TTImp -> LazyList Name
allVarNames expr = ttimp expr where mutual

  ttimp : TTImp -> LazyList Name
  ttimp $ IVar _ n                        = [n]
  ttimp $ IPi _ _ z _ argTy retTy         = ttimp argTy ++ ttimp retTy ++ piInfo z
  ttimp $ ILam _ _ z _ argTy lamTy        = ttimp argTy ++ ttimp lamTy ++ piInfo z
  ttimp $ ILet _ _ _ _ nTy nVal sc        = ttimp nTy ++ ttimp nVal ++ ttimp sc -- should we check `nTy` here?
  ttimp $ ICase _ _ ty xs                 = ttimp ty ++ assert_total (foldMap clause xs)
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
  decl $ IClaim _ _ _ _ t                     = ity t
  decl $ IData _ _ z                          = data_ z
  decl $ IDef _ _ xs                          = foldMap clause xs
  decl $ IParameters _ xs ys                  = lncpt xs ++ assert_total (foldMap decl ys)
  decl $ IRecord _ _ _ $ MkRecord _ _ ps _ fs = lncpt ps ++ foldMap (\(MkIField _ _ pii _ tt) => piInfo pii ++ ttimp tt) fs
  decl $ INamespace _ _ xs                    = assert_total $ foldMap decl xs
  decl $ ITransform _ _ z w                   = ttimp z ++ ttimp w
  decl $ IRunElabDecl _ y                     = ttimp y
  decl $ ILog _                               = []
  decl $ IBuiltin _ _ _                       = []

  data_ : Data -> LazyList Name
  data_ $ MkData x n tycon _ datacons = ttimp tycon ++ foldMap ity datacons
  data_ $ MkLater x n tycon           = ttimp tycon

  fieldUpdate : IFieldUpdate -> LazyList Name
  fieldUpdate $ ISetField    _ x = ttimp x
  fieldUpdate $ ISetFieldApp _ x = ttimp x

  clause : Clause -> LazyList Name
  clause $ PatClause _ lhs rhs          = ttimp lhs ++ ttimp rhs
  clause $ WithClause _ lhs wval _ _ xs = ttimp lhs ++ ttimp wval ++ assert_total (foldMap clause xs)
  clause $ ImpossibleClause _ lhs       = ttimp lhs

  piInfo : PiInfo TTImp -> LazyList Name
  piInfo ImplicitArg     = []
  piInfo ExplicitArg     = []
  piInfo AutoImplicit    = []
  piInfo (DefImplicit x) = ttimp x

export
hasNameInsideDeep : Elaboration m => Name -> TTImp -> m Bool
hasNameInsideDeep nm = assert_total holdsOnAnyInTrCl (== nm) namesOfType . toList . allVarNames where
  namesOfType : Name -> m $ List Name
  namesOfType n = try asIfType $ pure [] where
    asIfType : Elab $ List Name
    asIfType = do
      ty <- getInfo' n
      let subexprs = (map type ty.args) ++ (ty.cons >>= \con => con.type :: map type con.args)
      pure $ subexprs >>= toList . allVarNames

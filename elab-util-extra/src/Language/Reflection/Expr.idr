module Language.Reflection.Expr

import public Control.Applicative.Const -- public due to compiler's bug #2439

import public Data.Cozippable -- public due to compiler's bug #2439
import public Data.Fin.ToFin -- public due to compiler's bug #2439
import public Data.List.Ex -- public due to compiler's bug #2439
import public Data.SortedSet
import public Data.These -- public due to compiler's bug #2439
import public Data.Vect.Dependent

import public Language.Reflection
import public Language.Reflection.Syntax
import Language.Reflection.Syntax.Ops

import public Syntax.IHateParens.List

%default total

--------------------------
--- Namedness property ---
--------------------------

public export
data IsNamedArg : Arg -> Type where
  ItIsNamed : IsNamedArg $ MkArg cnt pii (Just n) ty

public export
isNamedArg : (arg : Arg) -> Dec $ IsNamedArg arg
isNamedArg (MkArg count piInfo (Just x) type) = Yes ItIsNamed
isNamedArg (MkArg count piInfo Nothing type)  = No $ \case ItIsNamed impossible

------------------------------------
--- General pure transformations ---
------------------------------------

public export
stname : Maybe Name -> Name
stname = fromMaybe $ UN Underscore

argName : (a : Arg) -> IsNamedArg a => Name
argName (MkArg _ _ Nothing _) impossible
argName (MkArg _ _ (Just x) _) = x

public export
argName' : Arg -> Name
argName' = stname . (.name)

export
cleanupNamedHoles : TTImp -> TTImp
cleanupNamedHoles = mapTTImp $ \case
  IHole {} => implicitFalse
  e        => e

----------------------------------------------
--- Compiler-based `TTImp` transformations ---
----------------------------------------------

export
normaliseAs' : Elaboration m =>
               (0 expected : Type) ->
               (preProcess : TTImp -> TTImp) ->
               {0 resulting : _} -> (0 postProcess : (x : expected) -> resulting x) ->
               TTImp -> m TTImp
normaliseAs' expected pre post expr = do
  let expr = cleanupNamedHoles expr
  expr' <- quote $ post !(check {expected} $ pre expr)
  let (args, _) = unPi expr
  let (args', ty) = unPi expr'
  let args'' = comergeWith (\pre => {name := pre.name}) args args'
  pure $ piAll ty args''

public export %inline
normaliseAs : Elaboration m => (0 expected : Type) -> TTImp -> m TTImp
normaliseAs ty = normaliseAs' ty id id

-- Normalises expression of any type; it is known to struggle with `let`s
public export %inline
normalise : Elaboration m => TTImp -> m TTImp
normalise = normaliseAs' (ty ** ty) (\expr => `((_ ** ~expr))) snd

-- More precise normalisation of type expressions
public export %inline
normaliseAsType : Elaboration m => TTImp -> m TTImp
normaliseAsType = normaliseAs Type

------------------------------------------------------------------------
--- Facilities for managing any kind of function application at once ---
------------------------------------------------------------------------

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

---------------------------------------
--- Building of special expressions ---
---------------------------------------

||| Lifts the given foldable of elements to an expression of a list-like data type
public export
liftList : Foldable f => f TTImp -> TTImp
liftList = foldr (\l, r => `(~l :: ~r)) `([])

||| Lifts the given foldable of elements to an expression of `Prelude.List`
public export
liftList' : Foldable f => f TTImp -> TTImp
liftList' = foldr (\l, r => `(Prelude.(::) ~l ~r)) `(Prelude.Nil)

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

-----------------------------------------------------
--- Analysis of pieces inside `TTImp` expressions ---
-----------------------------------------------------

||| Returns unnamespaced name and list of all namespaces stored in direct order
|||
||| Say, for `Data.Vect.Vect` it would return (["Data", "Vect"], `{Vect}).
export
unNS : Name -> (List String, Name)
unNS (NS (MkNS revNSs) nm) = mapFst (reverse revNSs ++) $ unNS nm
unNS (DN _ nm)             = unNS nm
unNS nm                    = ([], nm)

||| Returns all names that are suffixes of a given name (incuding the original name itself).
|||
||| For example, for the name `Data.Vect.Vect` suffixes set would include
||| `Data.Vect.Vect`, `Vect.Vect` and `Vect`.
export
allNameSuffixes : Name -> List Name
allNameSuffixes nm = do
  let (nss, n) = unNS nm
  tails nss <&> \case
    [] => n
    ns => NS (MkNS $ reverse ns) n

export
isNamespaced : Name -> Bool
isNamespaced = not . null . fst . unNS

public export
isImplicit : PiInfo c -> Bool
isImplicit ImplicitArg     = True
isImplicit (DefImplicit x) = True
isImplicit AutoImplicit    = True
isImplicit ExplicitArg     = False

-------------------------------------------------
--- Syntactic analysis of `TTImp` expressions ---
-------------------------------------------------

public export
isSameTypeAs : Name -> Name -> Elab Bool
isSameTypeAs n m = let eq = (==) `on` fst in [| lookupName n `eq` lookupName m |]

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
isVar : TTImp -> Bool
isVar $ IVar {} = True
isVar _         = False

public export
0 ArgDeps : Nat -> Type
ArgDeps n = DVect n $ SortedSet . Fin . Fin.finToNat

export
argDeps : (args : List Arg) -> ArgDeps args.length
argDeps args = do
  let nameToIndices = SortedMap.fromList $ mapI args $ \i, arg => (argName' arg, SortedSet.singleton i)
  let args = Vect.fromList args <&> \arg => allVarNames arg.type |> map (fromMaybe empty . lookup' nameToIndices)
  flip upmapI args $ \i, deps => flip concatMap deps $ \candidates =>
    maybe empty singleton $ last' $ mapMaybe tryToFit $ Prelude.toList candidates

export
dependees : (args : List Arg) -> SortedSet $ Fin $ args.length
dependees args = do
  let nameToIndex = SortedMap.fromList $ mapI args $ \i, arg => (argName' arg, i)
  let varsInTypes = concatMap (\arg => allVarNames' arg.type) args
  fromList $ mapMaybe (lookup' nameToIndex) $ Prelude.toList varsInTypes

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

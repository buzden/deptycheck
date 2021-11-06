module Test.DepTyCheck.Gen.Auto.Util.Reflection.Syntactic

import public Data.List.Lazy

import public Test.DepTyCheck.Gen.Auto.Util.Reflection

%default total

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

module Example.Pil.Gen

import Data.List

import Decidable.Equality

import public Example.Gen
import public Example.Pil

%default total

------------------
--- Generation ---
------------------

--- Expressions ---

export
constExprGen : Gen a -> Gen (Expression ctx a)
constExprGen = map C

maybeToList : Maybe a -> List a
maybeToList (Just x) = [x]
maybeToList Nothing = []

export
varExprGen' : {a : Type} -> {ctx : Context} -> DecEq Type => List (Expression ctx a)
varExprGen' = varExpressions {- this could be `oneOf $ map pure (fromList varExpressions)` if `Gen` could fail (contain zero) -} where
  varExpressions : List (Expression ctx a)
  varExpressions = map varExpr varsOfType where
    varExpr : (n : Name ** lk : Lookup n ctx ** reveal lk = a) -> Expression ctx a
    varExpr (n ** _ ** prf) = rewrite sym prf in V n

    varsOfType : List (n : Name ** lk : Lookup n ctx ** reveal lk = a)
    varsOfType = varsOfTypeOfCtx $ addLookups ctx
      where
        addLookups : (ctx : Context) -> List (n : Name ** ty : Type ** lk : Lookup n ctx ** reveal lk = ty)
        addLookups [] = []
        addLookups ((n, ty)::xs) = (n ** ty ** Here ty ** Refl) ::
                                   map (\(n ** ty ** lk ** lk_ty) => (n ** ty ** There lk ** lk_ty)) (addLookups xs)

        varsOfTypeOfCtx : List (n : Name ** ty : Type ** lk : Lookup n ctx ** reveal lk = ty) -> List (n : Name ** lk : Lookup n ctx ** reveal lk = a)
        varsOfTypeOfCtx [] = []
        varsOfTypeOfCtx ((n ** ty ** lk ** lk_ty)::xs) = maybeToList varX ++ varsOfTypeOfCtx xs where
          varX : Maybe (n : Name ** lk : Lookup n ctx ** reveal lk = a)
          varX = case decEq ty a of
            (Yes ty_a) => Just (n ** lk ** trans lk_ty ty_a)
            (No _) => Nothing

export
unaryExprGen : Gen (a -> a) -> Gen (Expression ctx a) -> Gen (Expression ctx a)
unaryExprGen gg sub = U <$> gg <*> sub

export
binaryExprGen : Gen (a -> a -> a) -> Gen (Expression ctx a) -> Gen (Expression ctx a)
binaryExprGen ggg sub = B <$> ggg <*> sub <*> sub

export
exprGen : (szBound : Nat) -> {a : Type} -> Gen a -> Gen (a -> a) -> Gen (a -> a -> a) -> {ctx : Context} -> DecEq Type => Gen (Expression ctx a)
exprGen Z g _ _ = oneOf $ [constExprGen g] ++ map pure (fromList varExprGen')
exprGen (S n) g gg ggg = oneOf [ exprGen (assert_smaller (S n) Z) g gg ggg
                               , unaryExprGen gg (exprGen n g gg ggg)
                               , binaryExprGen ggg (exprGen n g gg ggg)
                               ]

--- Statements ---

lookupGen : (ctx : Context) -> NonEmpty ctx => Gen (n : Name ** Lookup n ctx)
lookupGen ctx = let (lks@(_::_) ** _) = mapLk ctx in
                oneOf $ map pure $ fromList lks
  where
    mapLk : (ctx : Context) -> NonEmpty ctx => (l : List (n : Name ** Lookup n ctx) ** NonEmpty l)
    mapLk [(n, ty)] = ( [(n ** Here ty)] ** IsNonEmpty )
    mapLk ((n, ty)::xs@(_::_)) = ( (n ** Here ty) :: map (\(n ** lk) => (n ** There lk)) (fst $ mapLk xs) ** IsNonEmpty )

mutual

  export
  covering
  noDeclStmtGen : (ctx : Context) ->
                  Gen Type =>
                  Gen Name =>
                  (genExpr : {a : Type} -> {ctx : Context} -> Gen (Expression ctx a)) =>
                  Gen (Statement ctx ctx)
  noDeclStmtGen ctx = oneOf
    [ pure nop
    , case ctx of
      []     => pure nop -- this is returned because `oneOf` requires `Vect`, thus all cases must have equal size.
      (_::_) => do (n ** _) <- lookupGen ctx
                   pure $ n #= !genExpr
    , do (inside_for ** init) <- stmtGen ctx
         (_ ** body) <- stmtGen inside_for
         pure $ for init !genExpr !(noDeclStmtGen inside_for) body
    , pure $ if__ !genExpr (snd !(stmtGen ctx)) (snd !(stmtGen ctx))
    , pure $ !(noDeclStmtGen ctx) *> !(noDeclStmtGen ctx)
    , pure $ block $ snd !(stmtGen ctx)
    , pure $ print !(genExpr {a=String})
    ]

  export
  covering
  stmtGen : (pre : Context) ->
            (genTy : Gen Type) =>
            (genName : Gen Name) =>
            ({a : Type} -> {ctx : Context} -> Gen (Expression ctx a)) =>
            Gen (post ** Statement pre post)
  stmtGen pre = oneOf
    [ do s <- noDeclStmtGen pre
         pure (pre ** s)
    , do ty <- genTy
         n <- genName `suchThat` \nm => case lookup nm pre of Just _ => False; Nothing => True
         pure ((n, ty)::pre ** ty. n)
    , do (mid ** l) <- stmtGen pre
         (post ** r) <- stmtGen mid
         pure (post ** l *> r)
    ]

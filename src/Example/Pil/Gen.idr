module Example.Pil.Gen

import Data.List

import Decidable.Equality

import public Example.Gen
import public Example.Pil.Lang

%default total

------------------
--- Generation ---
------------------

--- Expressions ---

maybeToList : Maybe a -> List a
maybeToList (Just x) = [x]
maybeToList Nothing = []

export
varExprGen' : {a : Type'} -> {ctx : Context} -> List (Expression ctx a)
varExprGen' = varExpressions {- this could be `oneOf $ map pure (fromList varExpressions)` if `Gen` could fail (contain zero) -} where
  varExpressions : List (Expression ctx a)
  varExpressions = map varExpr varsOfType where
    varExpr : (n : Name ** lk : Lookup n ctx ** reveal lk = a) -> Expression ctx a
    varExpr (n ** _ ** prf) = rewrite sym prf in V n

    varsOfType : List (n : Name ** lk : Lookup n ctx ** reveal lk = a)
    varsOfType = varsOfTypeOfCtx $ addLookups ctx
      where
        addLookups : (ctx : Context) -> List (n : Name ** ty : Type' ** lk : Lookup n ctx ** reveal lk = ty)
        addLookups [] = []
        addLookups ((n, ty)::xs) = (n ** ty ** Here ty ** Refl) ::
                                   map (\(n ** ty ** lk ** lk_ty) => (n ** ty ** There lk ** lk_ty)) (addLookups xs)

        varsOfTypeOfCtx : List (n : Name ** ty : Type' ** lk : Lookup n ctx ** reveal lk = ty) -> List (n : Name ** lk : Lookup n ctx ** reveal lk = a)
        varsOfTypeOfCtx [] = []
        varsOfTypeOfCtx ((n ** ty ** lk ** lk_ty)::xs) = maybeToList varX ++ varsOfTypeOfCtx xs where
          varX : Maybe (n : Name ** lk : Lookup n ctx ** reveal lk = a)
          varX = case decEq ty a of
            (Yes ty_a) => Just (n ** lk ** trans lk_ty ty_a)
            (No _)     => Nothing

||| Generator of non-recursive expressions (thus those that can be used with zero recursion bound).
nonRec_exprGen : {a : Type'} -> {ctx : Context} -> Gen (idrTypeOf a) -> (n ** Vect n $ Gen $ Expression ctx a)
nonRec_exprGen g = ( _ ** [C <$> g] ++ map pure (fromList varExprGen') )

export
exprGen : (szBound : Nat) ->
          {a : Type'} ->
          ({b : Type'} -> Gen $ idrTypeOf b) ->
          {ctx : Context} ->
          ((subGen : {x : Type'} -> Gen $ Expression ctx x) -> {b : Type'} -> Gen $ Expression ctx b) ->
          Gen (Expression ctx a)
exprGen Z     g _   = oneOf $ snd $ nonRec_exprGen g
exprGen (S n) g rec = oneOf $ snd (nonRec_exprGen g) ++ [ rec (exprGen n g rec) ]

--- Universal patterns (particular cases) ---

asp : {0 indexed : index -> Type} ->
      {0 fin : {0 idx : index} -> indexed idx -> Type} ->
      Gen (n ** indexed n) ->
      ({0 idx : index} -> {p : indexed idx} -> Gen $ fin p) ->
      Gen (n : index ** p : indexed n ** fin p)
asp rl lr = do (n ** i) <- rl
               pure (n ** i ** !lr)

--- Statements ---

lookupGen : (ctx : Context) -> NonEmpty ctx => Gen (n : Name ** Lookup n ctx)
lookupGen ctx = let (lks@(_::_) ** _) = mapLk ctx in
                oneOf $ map pure $ fromList lks
  where
    mapLk : (ctx : Context) -> NonEmpty ctx => (l : List (n : Name ** Lookup n ctx) ** NonEmpty l)
    mapLk [(n, ty)] = ( [(n ** Here ty)] ** IsNonEmpty )
    mapLk ((n, ty)::xs@(_::_)) = ( (n ** Here ty) :: map (\(n ** lk) => (n ** There lk)) (fst $ mapLk xs) ** IsNonEmpty )

||| Statements generator of those that do not change the context and those that are not recursive.
noCtxChange_noRec_stmtGen : (ctx : Context) ->
                            (genExpr : {a : Type'} -> {ctx : Context} -> Gen (Expression ctx a)) =>
                            Vect 3 $ Gen (Statement ctx ctx)
noCtxChange_noRec_stmtGen ctx =
  [ pure nop
  , case ctx of
    []     => pure nop -- this is returned because `oneOf` requires `Vect`, thus all cases must have equal size.
    (_::_) => do (n ** _ ** e) <- asp (lookupGen ctx) genExpr
                 pure $ n #= e
  , do pure $ print !(genExpr {a=String'})
  ]

||| Statements generator of those that can change the context and those that are not recursive.
ctxChanging_noRec_stmtGen : (pre : Context) ->
                            (genTy : Gen Type') =>
                            (genName : Gen Name) =>
                            Gen (post ** Statement pre post)
ctxChanging_noRec_stmtGen pre = do
  ty <- genTy
  n <- genName
  pure ((n, ty)::pre ** ty. n)

mutual

  ||| Statements generator of those statements that can't change the context.
  export
  noCtxChange_stmtGen : (bound : Nat) ->
                        (ctx : Context) ->
                        Gen Type' =>
                        Gen Name =>
                        (genExpr : {a : Type'} -> {ctx : Context} -> Gen (Expression ctx a)) =>
                        Gen (Statement ctx ctx)
  noCtxChange_stmtGen Z     ctx = oneOf $ noCtxChange_noRec_stmtGen ctx
  noCtxChange_stmtGen (S n) ctx = oneOf $
    noCtxChange_noRec_stmtGen ctx ++
    [ do (inside_for ** init) <- stmtGen n ctx
         (_ ** body) <- stmtGen n inside_for
         pure $ for init !genExpr !(noCtxChange_stmtGen n inside_for) body
    , pure $ if__ !genExpr (snd !(stmtGen n ctx)) (snd !(stmtGen n ctx))
    , pure $ !(noCtxChange_stmtGen n ctx) *> !(noCtxChange_stmtGen n ctx)
    , pure $ block $ snd !(stmtGen n ctx)
    ]

  export
  stmtGen : (bound : Nat) ->
            (pre : Context) ->
            (genTy : Gen Type') =>
            (genName : Gen Name) =>
            ({a : Type'} -> {ctx : Context} -> Gen (Expression ctx a)) =>
            Gen (post ** Statement pre post)
  stmtGen Z     pre = oneOf $ [ctxChanging_noRec_stmtGen pre, pure (pre ** !(noCtxChange_stmtGen Z pre))]
  stmtGen (S n) pre = oneOf $
    [ctxChanging_noRec_stmtGen pre] ++
    [ pure (pre ** !(noCtxChange_stmtGen n pre))
    , do (mid ** l) <- stmtGen n pre
         (post ** r) <- stmtGen n mid
         pure (post ** l *> r)
    ]

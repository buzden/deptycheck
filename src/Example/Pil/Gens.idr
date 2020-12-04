module Example.Pil.Gens

import Data.DPair
import Data.List

import Decidable.Equality

import public Example.Pil.Lang

import public Test.DepTyCheck.Gen

%default total

------------------
--- Generation ---
------------------

--- Universal patterns (particular cases) ---

asp : {0 indexed : index -> Type} ->
      {0 fin : {0 idx : index} -> indexed idx -> Type} ->
      Gen (n ** indexed n) ->
      ({0 idx : index} -> {p : indexed idx} -> Gen $ fin p) ->
      Gen (n : index ** p : indexed n ** fin p)
asp rl lr = do (n ** i) <- rl
               pure (n ** i ** !lr)

--- Common ---

lookupGen : (ctx : Context) -> Gen (n : Name ** Lookup n ctx)
lookupGen ctx = uniform $ mapLk ctx where
  mapLk : (ctx : Context) -> List (n ** Lookup n ctx)
  mapLk []            = []
  mapLk ((n, ty)::xs) = (n ** Here ty) :: map (\(n ** lk) => (n ** There lk)) (mapLk xs)

--- Expressions ---

export
varExprGen : {a : Type'} -> {ctx : Context} -> Gen $ Expression ctx a
varExprGen = do Element (n ** _) prf <- lookupGen ctx `suchThat_invertedEq` a $ \(_ ** lk) => reveal lk
                pure rewrite prf in V n

||| Generator of non-recursive expressions (thus those that can be used with zero recursion bound).
nonRec_exprGen : {a : Type'} -> {ctx : Context} -> Gen (idrTypeOf a) -> Gen $ Expression ctx a
nonRec_exprGen g = [| C g |] <|> varExprGen

export
exprGen : (szBound : Nat) ->
          {a : Type'} ->
          ({b : Type'} -> Gen $ idrTypeOf b) ->
          {ctx : Context} ->
          ((subGen : {x : Type'} -> Gen $ Expression ctx x) -> {b : Type'} -> Gen $ Expression ctx b) ->
          Gen (Expression ctx a)
exprGen Z     g _   = nonRec_exprGen g
exprGen (S n) g rec = nonRec_exprGen g <|> rec (exprGen n g rec)

--- Statements ---

||| Statements generator of those that do not change the context and those that are not recursive.
noCtxChange_noRec_stmtGen : (ctx : Context) ->
                            (genExpr : {a : Type'} -> {ctx : Context} -> Gen (Expression ctx a)) =>
                            Gen (Statement ctx ctx)
noCtxChange_noRec_stmtGen ctx = oneOf
  [ pure nop
  , do (n ** _ ** e) <- asp (lookupGen ctx) genExpr
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
  noCtxChange_stmtGen Z     ctx = noCtxChange_noRec_stmtGen ctx
  noCtxChange_stmtGen (S n) ctx = noCtxChange_noRec_stmtGen ctx <|> oneOf
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
  stmtGen Z     pre = ctxChanging_noRec_stmtGen pre <|> pure (pre ** !(noCtxChange_stmtGen Z pre))
  stmtGen (S n) pre = ctxChanging_noRec_stmtGen pre <|> oneOf
    [ pure (pre ** !(noCtxChange_stmtGen n pre))
    , do (mid ** l) <- stmtGen n pre
         (post ** r) <- stmtGen n mid
         pure (post ** l *> r)
    ]

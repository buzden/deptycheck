module Example.Pil.Gens

import Data.DPair
import Data.List.Lazier

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

lookupGen : (vars : Variables) -> Gen (n : Name ** Lookup n vars)
lookupGen vars = uniform $ fromList $ mapLk vars where
  mapLk : (vars : Variables) -> List (n ** Lookup n vars)
  mapLk []            = []
  mapLk ((n, ty)::xs) = (n ** Here ty) :: map (\(n ** lk) => (n ** There lk)) (mapLk xs)

--- Expressions ---

export
varExprGen : {a : Type'} -> {vars : Variables} -> Gen $ Expression vars a
varExprGen = do Element (n ** _) prf <- lookupGen vars `suchThat_invertedEq` a $ \(_ ** lk) => reveal lk
                pure rewrite prf in V n

||| Generator of non-recursive expressions (thus those that can be used with zero recursion bound).
nonRec_exprGen : {a : Type'} -> {vars : Variables} -> Gen (idrTypeOf a) -> Gen $ Expression vars a
nonRec_exprGen g = [| C g |] <|> varExprGen

export
exprGen : (szBound : Nat) ->
          {a : Type'} ->
          ({b : Type'} -> Gen $ idrTypeOf b) ->
          {vars : Variables} ->
          ((subGen : {x : Type'} -> Gen $ Expression vars x) -> {b : Type'} -> Gen $ Expression vars b) ->
          Gen (Expression vars a)
exprGen Z     g _   = nonRec_exprGen g
exprGen (S n) g rec = nonRec_exprGen g <|> rec (exprGen n g rec)

--- Statements ---

||| Statements generator of those that do not change the context and those that are not recursive.
noVarsChange_noRec_stmtGen : (vars : Variables) ->
                             (genExpr : {a : Type'} -> {vars : Variables} -> Gen (Expression vars a)) =>
                             Gen (Statement vars vars)
noVarsChange_noRec_stmtGen vars = oneOf
  [ pure nop
  , do (n ** _ ** e) <- asp (lookupGen vars) genExpr
       pure $ n #= e
  , do pure $ print !(genExpr {a=String'})
  ]

||| Statements generator of those that can change the context and those that are not recursive.
varsChanging_noRec_stmtGen : (pre : Variables) ->
                             (genTy : Gen Type') =>
                             (genName : Gen Name) =>
                             Gen (post ** Statement pre post)
varsChanging_noRec_stmtGen pre = do
  ty <- genTy
  n <- genName
  pure ((n, ty)::pre ** ty. n)

mutual

  ||| Statements generator of those statements that can't change the context.
  export
  noVarsChange_stmtGen : (bound : Nat) ->
                         (vars : Variables) ->
                         Gen Type' =>
                          Gen Name =>
                         (genExpr : {a : Type'} -> {vars : Variables} -> Gen (Expression vars a)) =>
                         Gen (Statement vars vars)
  noVarsChange_stmtGen Z     vars = noVarsChange_noRec_stmtGen vars
  noVarsChange_stmtGen (S n) vars = noVarsChange_noRec_stmtGen vars <|> oneOf
    [ do (inside_for ** init) <- stmtGen n vars
         (_ ** body) <- stmtGen n inside_for
         pure $ for init !genExpr !(noVarsChange_stmtGen n inside_for) body
    , pure $ if__ !genExpr (snd !(stmtGen n vars)) (snd !(stmtGen n vars))
    , [| noVarsChange_stmtGen n vars *> noVarsChange_stmtGen n vars |]
    , (\st => block $ snd st) <$> stmtGen n vars
    ]

  export
  stmtGen : (bound : Nat) ->
            (pre : Variables) ->
            (genTy : Gen Type') =>
            (genName : Gen Name) =>
            ({a : Type'} -> {vars : Variables} -> Gen (Expression vars a)) =>
            Gen (post ** Statement pre post)
  stmtGen Z     pre = varsChanging_noRec_stmtGen pre <|> (\st => (pre ** st)) <$> noVarsChange_stmtGen Z pre
  stmtGen (S n) pre = varsChanging_noRec_stmtGen pre <|> (\st => (pre ** st)) <$> noVarsChange_stmtGen n pre
    <|> do (mid ** l) <- stmtGen n pre
           (post ** r) <- stmtGen n mid
           pure (post ** l *> r)

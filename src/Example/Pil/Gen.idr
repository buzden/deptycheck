module Example.Pil.Gen

import Decidable.Equality

import Example.Gen
import Example.Pil

%default total

------------------
--- Generation ---
------------------

--- Expressions ---

export
exprGen : (szBound : Nat) -> {a : Type} -> Gen a -> Gen (a -> a) -> Gen (a -> a -> a) -> {ctx : Context} -> DecEq Type => Gen (Expression ctx a)
exprGen Z g _ _ = oneOf $ [ C <$> g ] ++ map pure (fromList varExpressions)
  where
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

          maybeToList : Maybe b -> List b
          maybeToList (Just x) = [x]
          maybeToList Nothing = []

    varExpressions : List (Expression ctx a)
    varExpressions = map varExpr varsOfType where
      varExpr : (n : Name ** lk : Lookup n ctx ** reveal lk = a) -> Expression ctx a
      varExpr (n ** _ ** prf) = rewrite sym prf in V n

exprGen (S n) g gg ggg = oneOf [ exprGen (assert_smaller (S n) Z) g gg ggg
                               , U <$> gg <*> exprGen n g gg ggg
                               , B <$> ggg <*> exprGen n g gg ggg <*> exprGen n g gg ggg
                               ]

--- Statements ---



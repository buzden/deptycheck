module Example.Pil.Gens

import Data.DPair
import Data.List.Lazier
import Data.Fuel

import Decidable.Equality

import public Example.Pil.Lang

import public Test.DepTyCheck.Gen

%default total

------------------
--- Generation ---
------------------

--- General methodology of writing generators ---

-- Determine the desired (root) data component and its parameters.
-- Say, it is a `X (a : A) (b : B)`.
-- Determine which parameters finally would be user-defined and which are generated.
-- Say, `x` is user-defined and `y` is generated.
-- Then the type of the main generator would be `(a : A) -> Gen (b : B ** X a b)`.

-- Determine also the types which has external generators and add their `Gen Y =>` to the final signature.

-- For each constructor of the desired type (`X` in the example) do the following.
-- Determine its arguments
-- TBD

-- For recursion, mutuality or separate signature predeclaration is required.
-- The latter is, probably, the most universal way since it would always work
-- because there is no need of reduction of `Gen`-producing functions.

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
varExprGen : {a : Type'} -> {vars : Variables} -> {regs : Registers rc} -> Gen $ Expression vars regs a
varExprGen = do Element (n ** _) prf <- lookupGen vars `suchThat_invertedEq` a $ \(_ ** lk) => reveal lk
                pure rewrite prf in V n

||| Generator of non-recursive expressions (thus those that can be used with zero recursion bound).
nonRec_exprGen : {a : Type'} -> {vars : Variables} -> {regs : Registers rc} -> Gen (idrTypeOf a) -> Gen $ Expression vars regs a
nonRec_exprGen g = [| C g |] <|> varExprGen
                   -- TODO to add the register access expression

export
exprGen : (fuel : Fuel) ->
          {a : Type'} ->
          ({b : Type'} -> Gen $ idrTypeOf b) ->
          {vars : Variables} ->
          {regs : Registers rc} ->
          ((subGen : {x : Type'} -> Gen $ Expression vars regs x) -> {b : Type'} -> Gen $ Expression vars regs b) ->
          Gen (Expression vars regs a)
exprGen Dry      g _   = nonRec_exprGen g
exprGen (More f) g rec = nonRec_exprGen g <|> rec (exprGen f g rec)

--- Statements ---

-- `preV` and `preR` paremeters are considered to be used-defined.

public export
SpecGen : (Nat -> Type) -> Type
SpecGen res =
  (fuel : Fuel) ->
  {0 rc : Nat} ->
  Gen Type' =>
  Gen Name =>
  ({a : Type'} -> {vars : Variables} -> {regs : Registers rc} -> Gen (Expression vars regs a)) =>
  res rc

namespace ForStatement_UpdateArgument_Generation

  public export
  ForUpdArgGen : Type
  ForUpdArgGen = SpecGen \rc => (preV : Variables) -> (preR : Registers rc) -> Gen (newR ** (Statement preV preR preV newR, newR =%= preR))

  export nop_gen   : ForUpdArgGen
  export dot_gen   : ForUpdArgGen
  export ass_gen   : ForUpdArgGen
  export for_gen   : ForUpdArgGen
  export if_gen    : ForUpdArgGen
  export seq_gen   : ForUpdArgGen
  export block_gen : ForUpdArgGen
  export print_gen : ForUpdArgGen

  export
  for_upd_arg_gen : ForUpdArgGen
  for_upd_arg_gen Dry preV preR = nop_gen   Dry preV preR
                              <|> dot_gen   Dry preV preR
                              <|> ass_gen   Dry preV preR
                              <|> print_gen Dry preV preR
  for_upd_arg_gen (More f) preV preR = nop_gen   f preV preR
                                   <|> dot_gen   f preV preR
                                   <|> ass_gen   f preV preR
                                   <|> for_gen   f preV preR
                                   <|> if_gen    f preV preR
                                   <|> seq_gen   f preV preR
                                   <|> block_gen f preV preR
                                   <|> print_gen f preV preR

namespace ForStatement_BodyArgument_Generation

  public export
  ForBodyArgGen : Type
  ForBodyArgGen = SpecGen \rc => (preV : Variables) -> (preR : Registers rc) -> Gen (postV ** newR ** (Statement preV preR postV newR, newR =%= preR))

  export nop_gen   : ForBodyArgGen
  export dot_gen   : ForBodyArgGen
  export ass_gen   : ForBodyArgGen
  export for_gen   : ForBodyArgGen
  export if_gen    : ForBodyArgGen
  export seq_gen   : ForBodyArgGen
  export block_gen : ForBodyArgGen
  export print_gen : ForBodyArgGen

  export
  for_body_arg_gen : ForBodyArgGen
  for_body_arg_gen Dry preV preR = nop_gen   Dry preV preR
                               <|> dot_gen   Dry preV preR
                               <|> ass_gen   Dry preV preR
                               <|> print_gen Dry preV preR
  for_body_arg_gen (More f) preV preR = nop_gen   f preV preR
                                    <|> dot_gen   f preV preR
                                    <|> ass_gen   f preV preR
                                    <|> for_gen   f preV preR
                                    <|> if_gen    f preV preR
                                    <|> seq_gen   f preV preR
                                    <|> block_gen f preV preR
                                    <|> print_gen f preV preR

namespace Statement_Generation

  public export
  StmtGen : Type
  StmtGen = SpecGen \rc => (preV : Variables) -> (preR : Registers rc) -> Gen (postV ** postR ** Statement preV preR postV postR)

  export nop_gen   : StmtGen
  export dot_gen   : StmtGen
  export ass_gen   : StmtGen
  export for_gen   : StmtGen
  export if_gen    : StmtGen
  export seq_gen   : StmtGen
  export block_gen : StmtGen
  export print_gen : StmtGen

  export
  statement_gen : StmtGen
  statement_gen Dry preV preR = nop_gen   Dry preV preR
                            <|> dot_gen   Dry preV preR
                            <|> ass_gen   Dry preV preR
                            <|> print_gen Dry preV preR
  statement_gen (More f) preV preR = nop_gen   f preV preR
                                 <|> dot_gen   f preV preR
                                 <|> ass_gen   f preV preR
                                 <|> for_gen   f preV preR
                                 <|> if_gen    f preV preR
                                 <|> seq_gen   f preV preR
                                 <|> block_gen f preV preR
                                 <|> print_gen f preV preR

  nop_gen _ preV preR = pure (_ ** _ ** nop)

  dot_gen @{type'} @{name} @{_} _ preV preR = pure (_ ** _ ** !type'. !name)

  ass_gen @{_} @{_} @{expr} _ preV preR = do
    (n ** lk) <- lookupGen preV
    pure (_ ** _ ** n #= !expr)

  for_gen @{_} @{_} @{expr} f preV preR = do
    (insideV ** insideR ** init) <- statement_gen f preV preR
    (_ ** (upd, _)) <- for_upd_arg_gen f insideV insideR
    (_ ** _ ** (body, _)) <- for_body_arg_gen f insideV insideR
    pure (_ ** _ ** for init !expr upd body)

  if_gen @{_} @{_} @{expr} f preV preR = do
    (_ ** _ ** th) <- statement_gen f preV preR
    (_ ** _ ** el) <- statement_gen f preV preR
    pure (_ ** _ ** if__ !expr th el)

  seq_gen f preV preR = do
    (midV ** midR ** l) <- statement_gen f preV preR
    (_    ** _    ** r) <- statement_gen f midV midR
    pure (_ ** _ ** l *> r)

  block_gen f preV preR = do
    (_ ** _ ** s) <- statement_gen f preV preR
    pure (_ ** _ ** block s)

  print_gen @{_} @{_} @{expr} _ preV preR = pure (_ ** _ ** print !(expr {a=String'}))

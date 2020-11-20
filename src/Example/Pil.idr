-- Primitive Imperative Language --
module Example.Pil

import Data.List.Elem

%default total

------------------------------------------------------
--- Auxiliary data definitions and their instances ---
------------------------------------------------------

export
data Name = MkName String

%name Name n, m

export
FromString Name where
  fromString = MkName

--- Static context in terms of which we are formulating an invariant ---

public export
Context : Type
Context = List (Name, Type)

%name Context ctx

infix 6 `hasType`

public export
hasType : Name -> Type -> Context -> Type
hasType n ty = Elem (n, ty)

-- TODO `hasType` should consider only leftmost tuple with the given name.

-----------------------------------
--- The main language structure ---
-----------------------------------

public export
data Expression : (ctx : Context) -> (res : Type) -> Type where
  -- Constant expression
  C : (x : ty) -> Expression ctx ty
  -- Value of the variable
  V : (n : Name) -> (0 _ : n `hasType` ty $ ctx) => Expression ctx ty
  -- Unary operation over the result of another expression
  U : (f : a -> b) -> Expression ctx a -> Expression ctx b
  -- Binary operation over the results of two another expressions
  B : (f : a -> b -> c) -> Expression ctx a -> Expression ctx b -> Expression ctx c

export
relaxExprCtx : Expression ctx a -> Expression (add::ctx) a
relaxExprCtx (C x)     = C x
relaxExprCtx (V n)     = V n
relaxExprCtx (U f x)   = U f (relaxExprCtx x)
relaxExprCtx (B f x y) = B f (relaxExprCtx x) (relaxExprCtx y)

infix 2 |=, !!=
infixr 1 *>

public export
data Statement : (pre : Context) -> (post : Context) -> Type where
  var : (n : Name) -> (0 ty : Type) -> {0 ctx : Context} -> Statement ctx $ ((n, ty) :: ctx)
  (|=) : (n : Name) -> (v : Expression ctx ty) -> (0 _ : n `hasType` ty $ ctx) => Statement ctx ctx
  for : (init : Statement outer_ctx inside_for)
     -> (cond : Expression inside_for Bool)
     -> (upd  : Statement inside_for inside_for)
     -> (body : Statement inside_for after_body)
     -> Statement outer_ctx outer_ctx
  if_  : (cond : Expression ctx Bool) -> Statement ctx ctx_then -> Statement ctx ctx
  if__ : (cond : Expression ctx Bool) -> Statement ctx ctx_then -> Statement ctx ctx_else -> Statement ctx ctx
  (*>) : Statement pre mid -> Statement mid post -> Statement pre post
  block : Statement outer inside -> Statement outer outer

(>>=) : Statement pre mid -> (Unit -> Statement mid post) -> Statement pre post
a >>= f = a *> f ()

-- Define and assign immediately
public export
(!!=) : (n : Name) -> Expression ctx ty -> Statement ctx $ ((n, ty) :: ctx)
n !!= v = var n ty *> n |= relaxExprCtx v

namespace AlternativeDefineAndAssign

  public export
  (|=) : (p : (Name, Type)) -> Expression ctx (snd p) -> Statement ctx $ (p :: ctx)
  (n, _) |= v = n !!= v

  public export
  (.) : a -> b -> (b, a)
  (.) a b = (b, a)

-------------------------
--- Examples of usage ---
-------------------------

(+) : Expression ctx Int -> Expression ctx Int -> Expression ctx Int
(+) = B (+)

(<) : Expression ctx Int -> Expression ctx Int -> Expression ctx Bool
(<) = B (<)

i : Int -> Expression ctx Int
i = C

simple_ass : Statement ctx $ ("x", Int)::ctx
simple_ass = do
  var "x" Int
  "x" |= i 2

lost_block : Statement ctx ctx
lost_block = block $ do
               var "x" Int
               "x" |= i 2
               Int. "y" |= V "x"
               Int. "z" |= C 3

some_for : Statement ctx ctx
some_for = for (do Int. "x" |= i 0; Int. "y" |= i 0) (V "x" < i 5) ("x" |= V "x" + i 1) $ do
             "y" |= V "y" + V "x" + i 1

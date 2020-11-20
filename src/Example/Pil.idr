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

infix 2 :-

public export
data Statement : (pre : Context) -> (post : Context) -> Type where
  var : (n : Name) -> (0 ty : Type) -> {0 ctx : Context} -> Statement ctx $ ((n, ty) :: ctx)
  (:-) : (n : Name) -> (v : Expression ctx ty) -> (0 _ : n `hasType` ty $ ctx) => Statement ctx ctx
  for : (init : Statement outer_ctx inside_for)
     -> (cond : Expression inside_for Bool)
     -> (upd  : Statement inside_for inside_for)
     -> (body : Statement inside_for after_body)
     -> Statement outer_ctx outer_ctx
  (>>=) : Statement pre mid -> Statement mid post -> Statement pre post
  block : Statement outer inside -> Statement outer outer

-------------------------
--- Examples of usage ---
-------------------------

(+) : Expression ctx Int -> Expression ctx Int -> Expression ctx Int
(+) = B (+)

(<) : Expression ctx Int -> Expression ctx Int -> Expression ctx Bool
(<) = B (<)

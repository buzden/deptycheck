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

export
record Context where
  constructor Ctx
  vars : List (Name, Type)

%name Context ctx

infix 6 `hasType`

public export
hasType : Name -> Type -> Context -> Type
hasType n ty ctx = Elem (n, ty) ctx.vars

-- TODO `hasType` should consider only leftmost tuple with the given name.

--------------------------------------
--- Nicely named logic definitions ---
--------------------------------------

public export
Always : a -> Type
Always = const Unit

public export
(&&) : (a -> Type) -> (a -> Type) -> a -> Type
(&&) f g = \x => (f x, g x)

-----------------------------------
--- The main language structure ---
-----------------------------------

public export
data Expression : (pre : Context -> Type) -> (res : Type) -> Type where
  -- Constant expression
  C : (x : ty) -> Expression Always ty
  -- Value of the variable
  V : (n : Name) -> Expression (n `hasType` ty) ty
  -- Unary operation over the result of another expression
  U : (f : a -> b) -> Expression pre a -> Expression pre b
  -- Binary operation over the results of two another expressions
  B : (f : a -> b -> c) -> Expression pre_a a -> Expression pre_b b -> Expression (pre_a && pre_b) c

infix 2 :-

public export
data Statement : (pre : Context -> Type) -> (eff : Context -> Context) -> Type where
  var : (n : Name) -> (ty : Type) -> Statement Always record {vars $= ((n, ty) ::)}
  (:-) : (n : Name) -> (v : Expression exp_pre ty) -> Statement (exp_pre && n `hasType` ty) id
  for : (init : Statement i_pre i_eff)
     -> (cond : Expression exp_pre Bool)
     -> (upd  : Statement upd_pre id)
     -> (body : Statement bd_pre id)
     -> Statement (ini_pre && (cond_pre && upd_pre && body_pre) . ini_eff) id
  (>>=) : Statement l_pre l_eff -> Statement r_pre r_eff -> Statement (l_pre && r_pre . l_eff) (r_eff . l_eff)
  block : {0 eff : Context -> Context} -> Statement pre eff -> Statement pre id

  -- actually, if context could be more than defined variables, then instead of `id`s we'd write something like `(\ctx => record {vars = ctx.vars} (eff ctx))`

0 alternative_tupling : {0 ini_pre, cond_pre, upd_pre, body_pre  : Context -> Type} -> {0 ini_eff : Context -> Context}
            -> ini_pre && (cond_pre && upd_pre && body_pre) . ini_eff
                 =
               \original_ctx => let working_ctx = ini_eff original_ctx in
                 (ini_pre original_ctx, cond_pre working_ctx, upd_pre working_ctx, body_pre working_ctx)
alternative_tupling = Refl


-- Example of lifting the binary function into the `Expression` world.
--(+) : Expression pa Int -> Expression pb Int -> Expression (pa && pb) Int
--(+) = B (+)

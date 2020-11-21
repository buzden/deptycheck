-- Primitive Imperative Language --
module Example.Pil

import Data.List
import Data.List.Elem
import Data.Maybe

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

export
Eq Name where
  MkName n == MkName m = n == m

--- Static context in terms of which we are formulating an invariant ---

public export
Context : Type
Context = List (Name, Type)

%name Context ctx

-----------------------------------------------
--- List lookup with propositional equality ---
-----------------------------------------------

public export
data Lookup : a -> List (a, b) -> Type where
  Here : (y : b) -> Lookup x $ (x, y)::xys
  There : Lookup z xys -> Lookup z $ (x, y)::xys

public export
reveal : Lookup {b} x xys -> b
reveal (Here y) = y
reveal (There subl) = reveal subl

-----------------------------------
--- The main language structure ---
-----------------------------------

public export
data Expression : (ctx : Context) -> (res : Type) -> Type where
  -- Constant expression
  C : (x : ty) -> Expression ctx ty
  -- Value of the variable
  V : (n : Name) -> (0 ty : Lookup n ctx) => Expression ctx $ reveal ty
  -- Unary operation over the result of another expression
  U : (f : a -> b) -> Expression ctx a -> Expression ctx b
  -- Binary operation over the results of two another expressions
  B : (f : a -> b -> c) -> Expression ctx a -> Expression ctx b -> Expression ctx c

infix 2 #=, ?#=
infixr 1 *>

public export
data Statement : (pre : Context) -> (post : Context) -> Type where
  nop  : Statement ctx ctx
  (.)  : (0 ty : Type) -> (n : Name) -> Statement ctx $ (n, ty)::ctx
  (#=) : (n : Name) -> (0 ty : Lookup n ctx) => (v : Expression ctx $ reveal ty) -> Statement ctx ctx
  for  : (init : Statement outer_ctx inside_for)  -> (cond : Expression inside_for Bool)
      -> (upd  : Statement inside_for inside_for) -> (body : Statement inside_for after_body)
      -> Statement outer_ctx outer_ctx
  if__ : (cond : Expression ctx Bool) -> Statement ctx ctx_then -> Statement ctx ctx_else -> Statement ctx ctx
  (*>) : Statement pre mid -> Statement mid post -> Statement pre post
  block : Statement outer inside -> Statement outer outer
  print : Show ty => Expression ctx ty -> Statement ctx ctx

public export %inline
(>>=) : Statement pre mid -> (Unit -> Statement mid post) -> Statement pre post
a >>= f = a *> f ()

public export %inline
if_  : (cond : Expression ctx Bool) -> Statement ctx ctx_then -> Statement ctx ctx
if_ c t = if__ c t nop

-- Define with derived type and assign immediately
public export %inline
(?#=) : (n : Name) -> Expression ((n, ty)::ctx) ty -> Statement ctx $ (n, ty)::ctx
n ?#= v = ty. n *> n #= v

namespace AlternativeDefineAndAssign

  public export %inline
  (#=) : (p : (Name, Type)) -> Expression (p::ctx) (snd p) -> Statement ctx $ p::ctx
  (n, _) #= v = n ?#= v

  public export %inline
  (.) : a -> b -> (b, a)
  (.) a b = (b, a)

-------------------------
--- Examples of usage ---
-------------------------

--- Functions lifted to the expression level ---

export %inline
(+) : Expression ctx Int -> Expression ctx Int -> Expression ctx Int
(+) = B (+)

export %inline
(<) : Expression ctx Int -> Expression ctx Int -> Expression ctx Bool
(<) = B (<)

export %inline
(&&) : Expression ctx Bool -> Expression ctx Bool -> Expression ctx Bool
(&&) = B (\a, b => a && b) -- recoded because of laziness

export %inline
(++) : Expression ctx String -> Expression ctx String -> Expression ctx String
(++) = B (++)

export %inline
show : Show ty => Expression ctx ty -> Expression ctx String
show = U show

--- Example statements ---

simple_ass : Statement ctx $ ("x", Int)::ctx
simple_ass = do
  Int. "x"
  "x" #= C 2

lost_block : Statement ctx ctx
lost_block = block $ do
               Int. "x"
               "x" #= C 2
               Int. "y" #= V "x"
               Int. "z" #= C 3
               print $ V "y" + V "z" + V "x"

some_for : Statement ctx ctx
some_for = for (do Int. "x" #= C 0; Int. "y" #= C 0) (V "x" < C 5 && V "y" < C 10) ("x" #= V "x" + C 1) $ do
             "y" #= V "y" + V "x" + C 1

name_shadowing : Statement ctx ctx
name_shadowing = block $ do
  Int. "x" #= C 3
  Int. "y" #= V "x" + C 2
  String. "x" #= C "foo"
  --print $ V "x" ++ C "bar" ++ show (V "y") -- addition of [search x] to `Lookup` fixes this but breaks `There` cases in other places (e.g. `V "y"` above).

module Example.Pil.Lang

import Decidable.Equality

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

--- Available types in the system ---

public export
data Type' = Bool' | Int' | String'

public export
idrTypeOf : Type' -> Type
idrTypeOf Bool'   = Bool
idrTypeOf Int'    = Int
idrTypeOf String' = String

export
DecEq Type' where
  decEq Bool'   Bool'   = Yes Refl
  decEq Int'    Int'    = Yes Refl
  decEq String' String' = Yes Refl

  decEq Bool'   Int'    = No $ \case Refl impossible
  decEq Bool'   String' = No $ \case Refl impossible

  decEq Int'    Bool'   = No $ \case Refl impossible
  decEq Int'    String' = No $ \case Refl impossible

  decEq String' Bool'   = No $ \case Refl impossible
  decEq String' Int'    = No $ \case Refl impossible

--- Static context for formulating an invariant ---

public export
Context : Type
Context = List (Name, Type')

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
data Expression : (ctx : Context) -> (res : Type') -> Type where
  -- Constant expression
  C : {ty : Type'} -> (x : idrTypeOf ty) -> Expression ctx ty
  -- Value of the variable
  V : (n : Name) -> (0 lk : Lookup n ctx) => Expression ctx $ reveal lk
  -- Unary operation over the result of another expression
  U : {default "?func" opName : String} -> (f : idrTypeOf a -> idrTypeOf b) -> Expression ctx a -> Expression ctx b
  -- Binary operation over the results of two another expressions
  B : {default "??" opName : String} -> (f : idrTypeOf a -> idrTypeOf b -> idrTypeOf c) -> Expression ctx a -> Expression ctx b -> Expression ctx c

infix 2 #=, ?#=
infixr 1 *>

public export
data Statement : (pre : Context) -> (post : Context) -> Type where
  nop  : Statement ctx ctx
  (.)  : (ty : Type') -> (n : Name) -> Statement ctx $ (n, ty)::ctx
  (#=) : (n : Name) -> (0 lk : Lookup n ctx) => (v : Expression ctx $ reveal lk) -> Statement ctx ctx
  for  : (init : Statement outer_ctx inside_for)  -> (cond : Expression inside_for Bool') ->
         (upd  : Statement inside_for inside_for) -> (body : Statement inside_for after_body) ->
         Statement outer_ctx outer_ctx
  if__ : (cond : Expression ctx Bool') -> Statement ctx ctx_then -> Statement ctx ctx_else -> Statement ctx ctx
  (*>) : Statement pre mid -> Statement mid post -> Statement pre post
  block : Statement outer inside -> Statement outer outer
  print : Show (idrTypeOf ty) => Expression ctx ty -> Statement ctx ctx

public export %inline
(>>=) : Statement pre mid -> (Unit -> Statement mid post) -> Statement pre post
a >>= f = a *> f ()

public export %inline
if_  : (cond : Expression ctx Bool') -> Statement ctx ctx_then -> Statement ctx ctx
if_ c t = if__ c t nop

public export %inline
while : Expression ctx Bool' -> Statement ctx after_body -> Statement ctx ctx
while cond = for nop cond nop

-- Define with derived type and assign immediately
public export %inline
(?#=) : (n : Name) -> {ty : Type'} -> Expression ((n, ty)::ctx) ty -> Statement ctx $ (n, ty)::ctx
n ?#= v = ty. n *> n #= v

namespace AlternativeDefineAndAssign

  public export %inline
  (#=) : (p : (Name, Type')) -> Expression (p::ctx) (snd p) -> Statement ctx $ p::ctx
  (n, _) #= v = n ?#= v

  public export %inline
  (.) : a -> b -> (b, a)
  (.) a b = (b, a)

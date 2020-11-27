-- Primitive Imperative Language --
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

--- Static context in terms of which we are formulating an invariant ---

public export
Context : Type
Context = List (Name, Type')

%name Context ctx

-----------------------------------------------
--- List lookup with propositional equality ---
-----------------------------------------------

public export
data Lookup : a -> List (a, b) -> Type where
  There : Lookup z xys -> Lookup z $ (x, y)::xys
  Here : (y : b) -> Lookup x $ (x, y)::xys
  -- !!! Idris searches from the bottom !!!

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
  for  : (init : Statement outer_ctx inside_for)  -> (cond : Expression inside_for Bool')
      -> (upd  : Statement inside_for inside_for) -> (body : Statement inside_for after_body)
      -> Statement outer_ctx outer_ctx
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

-------------------------
--- Examples of usage ---
-------------------------

--- Functions lifted to the expression level ---

export %inline
(+) : Expression ctx Int' -> Expression ctx Int' -> Expression ctx Int'
(+) = B (+) {opName="+"}

export %inline
div : Expression ctx Int' -> Expression ctx Int' -> Expression ctx Int'
div = B div {opName="/"}

export %inline
mod : Expression ctx Int' -> Expression ctx Int' -> Expression ctx Int'
mod = B mod {opName="%"}

export %inline
(<) : Expression ctx Int' -> Expression ctx Int' -> Expression ctx Bool'
(<) = B (<) {opName="<"}

export %inline
(>) : Expression ctx Int' -> Expression ctx Int' -> Expression ctx Bool'
(>) = B (>) {opName=">"}

export %inline
(==) : Eq (idrTypeOf a) => Expression ctx a -> Expression ctx a -> Expression ctx Bool'
(==) = B (==) {opName="=="}

export %inline
(/=) : Eq (idrTypeOf a) => Expression ctx a -> Expression ctx a -> Expression ctx Bool'
(/=) = B (/=) {opName="!="}

export %inline
(&&) : Expression ctx Bool' -> Expression ctx Bool' -> Expression ctx Bool'
(&&) = B (\a, b => a && b) {opName="&&"} -- recoded because of laziness

export %inline
(++) : Expression ctx String' -> Expression ctx String' -> Expression ctx String'
(++) = B (++) {opName="??concat??"}

export %inline
show : Show (idrTypeOf ty) => Expression ctx ty -> Expression ctx String'
show = U show {opName="toString"}

--- Example statements ---

simple_ass : Statement ctx $ ("x", Int')::ctx
simple_ass = do
  Int'. "x"
  "x" #= C 2

lost_block : Statement ctx ctx
lost_block = do
  block $ do
    Int'. "x"
    "x" #= C 2
    Int'. "y" #= V "x"
    Int'. "z" #= C 3
    print $ V "y" + V "z" + V "x"

some_for : Statement ctx ctx
some_for = for (do Int'. "x" #= C 0; Int'. "y" #= C 0) (V "x" < C 5 && V "y" < C 10) ("x" #= V "x" + C 1) $ do
             "y" #= V "y" + V "x" + C 1

--bad_for : Statement ctx ctx
--bad_for = for (do Int'. "x" #= C 0; Int'. "y" #= C 0)
--                (V "y")
--                  ("x" #= V "x" + C 1) $ do
--             "y" #= V "y" `div` V "x" + C 1

euc : {0 ctx : Context} -> let c = ("a", Int')::("b", Int')::ctx in Statement c $ ("res", Int')::c
euc = do
  while (V "a" /= C 0 && V "b" /= C 0) $ do
    if__ (V "a" > V "b")
      ("a" #= V "a" `mod` V "b")
      ("b" #= V "b" `mod` V "a")
  Int'. "res" #= V "a" + V "b"

name_shadowing : Statement ctx ctx
name_shadowing = block $ do
  Int'. "x" #= C 0
  block $ do
    Int'. "x" #= C 3
    Int'. "y" #= V "x" + C 2
    String'. "x" #= C "foo"
    print $ V "x" ++ C "bar" ++ show (V "y")
  Int'. "z" #= V "x" + C 2

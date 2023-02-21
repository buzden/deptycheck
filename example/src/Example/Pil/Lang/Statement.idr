module Example.Pil.Lang.Statement

import public Data.List.Lookup

import public Example.Pil.Lang.Expression

%default total

infix 2 #=, ?#=, !#=, %=

public export
data Statement : (preV  : Variables) -> (preR  : Registers rc) ->
                 (postV : Variables) -> (postR : Registers rc) ->
                 Type where

  Nop  : Statement vars regs vars regs

  (.)  : (ty : Type') -> (n : Name) -> Statement vars regs ((n, ty)::vars) regs

  (#=) : (n : Name) -> (0 lk : Lookup n vars) => (v : Expression vars regs lk.reveal) ->
         Statement vars regs vars regs

  (%=) : {0 preR : Registers rc} ->
         (reg : Fin rc) -> Expression vars preR ty ->
         Statement vars preR vars $ preR `With` (reg, Just ty)

  For  : (init : Statement preV preR insideV insideR) ->
         (cond : Expression insideV insideR Bool') ->
         (upd  : Statement insideV insideR insideV updR) ->
         (0 _ : updR =%= insideR) =>
         (body : Statement insideV insideR postBodyV bodyR) ->
         (0 _ : bodyR =%= insideR) =>
         Statement preV preR preV insideR
         -- Registers that are changed in `upd` or `body` must be unavailable in `cond`, `upd`, `body` and `for` itself
         -- in the case when we allow `upd` and `body` to change register types.

  If__ : (cond : Expression vars regs Bool') ->
         Statement vars regs varsThen regsThen ->
         Statement vars regs varsElse regsElse ->
         Statement vars regs vars $ Merge regsThen regsElse

  (>>) : Statement preV preR midV midR ->
         Statement midV midR postV postR ->
         Statement preV preR postV postR

  Block : Statement preV preR insideV postR -> Statement preV preR preV postR

  Print : Show (idrTypeOf ty) => Expression vars regs ty -> Statement vars regs vars regs

public export %inline
nop  : Statement vars regs vars regs
nop = Nop

public export %inline
for  : (init : Statement preV preR insideV insideR) ->
       (cond : Expression insideV insideR Bool') ->
       (upd  : Statement insideV insideR insideV updR) ->
       (0 _ : updR =%= insideR) =>
       (body : Statement insideV insideR postBodyV bodyR) ->
       (0 _ : bodyR =%= insideR) =>
       Statement preV preR preV insideR
for = For

public export %inline
if__ : (cond : Expression vars regs Bool') ->
       Statement vars regs varsThen regsThen ->
       Statement vars regs varsElse regsElse ->
       Statement vars regs vars $ Merge regsThen regsElse
if__ = If__

public export %inline
block : Statement preV preR insideV postR -> Statement preV preR preV postR
block = Block

public export %inline
print : Show (idrTypeOf ty) => Expression vars regs ty -> Statement vars regs vars regs
print = Print

public export %inline
(>>=) : Statement preV preR midV midR ->
        (Unit -> Statement midV midR postV postR) ->
        Statement preV preR postV postR
a >>= f = a >> f ()

public export %inline
if_  : (cond : Expression vars regsBefore Bool') ->
       Statement vars regsBefore varsThen regsThen ->
       Statement vars regsBefore vars $ Merge regsThen regsBefore
if_ c t = if__ c t nop

public export %inline
while : Expression vars regs Bool' ->
        Statement vars regs after_body body_regs ->
        (0 _ : body_regs =%= regs) =>
        Statement vars regs vars regs
while cond body = for nop cond nop body

-- Define with derived type and assign immediately
public export %inline
(?#=) : (n : Name) -> {ty : Type'} -> {0 regs : Registers rc} ->
        Expression ((n, ty)::vars) regs ty -> Statement vars regs ((n, ty)::vars) regs
n ?#= v = ty. n >> n #= v

namespace AlternativeDefineAndAssign

  public export %inline
  (!#=) : (p : (Name, Type')) -> Expression (p::vars) regs (snd p) -> Statement vars regs (p::vars) regs
  (n, _) !#= v = n ?#= v

  public export %inline
  (.) : a -> b -> (b, a)
  (.) a b = (b, a)

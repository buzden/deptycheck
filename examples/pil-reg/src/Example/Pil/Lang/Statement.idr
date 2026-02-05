module Example.Pil.Lang.Statement

import public Data.List.Lookup

import public Example.Pil.Lang.Expression

%default total

export infix 2 #=, ?#=, !#=, %=

public export
data Statement : Ops ->
                 (preV  : Variables) -> (preR  : Registers rc) ->
                 (postV : Variables) -> (postR : Registers rc) ->
                 Type where

  Nop  : Statement ops vars regs vars regs

  (.)  : (ty : Type') -> (n : Name) -> Statement ops vars regs ((n, ty)::vars) regs

  (#=) : (n : Name) -> (0 lk : Lookup n vars) => (v : Expression ops vars regs lk.reveal) ->
         Statement ops vars regs vars regs

  (%=) : {0 preR : Registers rc} ->
         (reg : Fin rc) -> Expression ops vars preR ty ->
         Statement ops vars preR vars $ preR `With` (reg, Just ty)

  For  : (init : Statement ops preV preR insideV insideR) ->
         (cond : Expression ops insideV insideR Bool') ->
         (upd  : Statement ops insideV insideR insideV updR) ->
         (0 _ : updR =%= insideR) =>
         (body : Statement ops insideV insideR postBodyV bodyR) ->
         (0 _ : bodyR =%= insideR) =>
         Statement ops preV preR preV insideR
         -- Registers that are changed in `upd` or `body` must be unavailable in `cond`, `upd`, `body` and `for` itself
         -- in the case when we allow `upd` and `body` to change register types.

  If__ : (cond : Expression ops vars regs Bool') ->
         Statement ops vars regs varsThen regsThen ->
         Statement ops vars regs varsElse regsElse ->
         Statement ops vars regs vars $ Merge regsThen regsElse

  (>>) : Statement ops preV preR midV midR ->
         Statement ops midV midR postV postR ->
         Statement ops preV preR postV postR

  Block : Statement ops preV preR insideV postR -> Statement ops preV preR preV postR

  Print : Expression ops vars regs ty -> Statement ops vars regs vars regs

public export %inline
nop  : Statement ops vars regs vars regs
nop = Nop

public export %inline
for  : (init : Statement ops preV preR insideV insideR) ->
       (cond : Expression ops insideV insideR Bool') ->
       (upd  : Statement ops insideV insideR insideV updR) ->
       (0 _ : updR =%= insideR) =>
       (body : Statement ops insideV insideR postBodyV bodyR) ->
       (0 _ : bodyR =%= insideR) =>
       Statement ops preV preR preV insideR
for = For

public export %inline
if__ : (cond : Expression ops vars regs Bool') ->
       Statement ops vars regs varsThen regsThen ->
       Statement ops vars regs varsElse regsElse ->
       Statement ops vars regs vars $ Merge regsThen regsElse
if__ = If__

public export %inline
block : Statement ops preV preR insideV postR -> Statement ops preV preR preV postR
block = Block

public export %inline
print : Expression ops vars regs ty -> Statement ops vars regs vars regs
print = Print

public export %inline
(>>=) : Statement ops preV preR midV midR ->
        (Unit -> Statement ops midV midR postV postR) ->
        Statement ops preV preR postV postR
a >>= f = a >> f ()

public export %inline
if_  : (cond : Expression ops vars regsBefore Bool') ->
       Statement ops vars regsBefore varsThen regsThen ->
       Statement ops vars regsBefore vars $ Merge regsThen regsBefore
if_ c t = if__ c t nop

public export %inline
while : Expression ops vars regs Bool' ->
        Statement ops vars regs after_body body_regs ->
        (0 _ : body_regs =%= regs) =>
        Statement ops vars regs vars regs
while cond body = for nop cond nop body

-- Define with derived type and assign immediately
public export %inline
(?#=) : (n : Name) -> {ty : Type'} -> {0 regs : Registers rc} ->
        Expression ops ((n, ty)::vars) regs ty -> Statement ops vars regs ((n, ty)::vars) regs
n ?#= v = ty. n >> n #= v

namespace AlternativeDefineAndAssign

  public export %inline
  (!#=) : (p : (Name, Type')) -> Expression ops (p::vars) regs (snd p) -> Statement ops vars regs (p::vars) regs
  (n, _) !#= v = n ?#= v

  public export %inline
  (.) : a -> b -> (b, a)
  (.) a b = (b, a)

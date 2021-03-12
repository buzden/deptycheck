module Example.Pil.Lang.Statement

import Data.List.Lookup

import Data.String.Extra

import Example.Pil.Lang.Common
import Example.Pil.Lang.Expression

%default total

infix 2 #=, ?#=, !#=, %=
infixr 1 *>

data Statement : (preV : Variables) -> (preR : Registers rc) -> (postV : Variables) -> (postR : Registers rc) -> Type

public export %inline
0 (.varsAfter) : Statement preV preR postV postR -> Variables
stmt.varsAfter = postV

public export %inline
0 (.regsAfter) : {0 preR : Registers rc} -> Statement preV preR postV postR -> Registers rc
stmt.regsAfter = postR

public export
data Statement : (preV : Variables) -> (preR : Registers rc) -> (postV : Variables) -> (postR : Registers rc) -> Type where
  nop  : Statement vars regs vars regs

  (.)  : (ty : Type') -> (n : Name) -> Statement vars regs ((n, ty)::vars) regs

  (#=) : (n : Name) -> (0 lk : Lookup n vars) => (v : Expression vars regs lk.reveal) -> Statement vars regs vars regs

  (%=) : {0 preR : Registers rc} ->
         (reg : Fin rc) -> Expression vars preR ty -> Statement vars preR vars $ preR `With` (reg, Just ty)

  for  : (init : Statement preV preR insideV insideR) ->
         (cond : Expression insideV insideR Bool') ->
         (upd  : Statement insideV insideR insideV updR) ->
         (0 _ : updR =%= insideR) =>
         (body : Statement insideV insideR postBodyV bodyR) ->
         (0 _ : bodyR =%= insideR) =>
         Statement preV preR preV insideR
         -- Registers that are changed in `upd` or `body` must be unavailable in `cond`, `upd`, `body` and `for` itself
         -- in the case when we allow `upd` and `body` to change register types.

  if__ : (cond : Expression vars regs Bool') ->
         Statement vars regs varsThen regsThen ->
         Statement vars regs varsElse regsElse ->
         Statement vars regs vars $ Merge regsThen regsElse

  (*>) : Statement preV preR midV midR ->
         Statement midV midR postV postR ->
         Statement preV preR postV postR

  block : Statement preV preR insideV postR -> Statement preV preR preV postR

  print : Show (idrTypeOf ty) => Expression vars regs ty -> Statement vars regs vars regs

public export %inline
(>>) : Statement preV preR midV midR -> Statement midV midR postV postR -> Statement preV preR postV postR
(>>) = (*>)

public export %inline
(>>=) : Statement preV preR midV midR -> (Unit -> Statement midV midR postV postR) -> Statement preV preR postV postR
a >>= f = a *> f ()

public export %inline
if_  : (cond : Expression vars regsBefore Bool') -> Statement vars regsBefore varsThen regsThen -> Statement vars regsBefore vars $ Merge regsThen regsBefore
if_ c t = if__ c t nop

public export %inline
while : Expression vars regs Bool' -> Statement vars regs after_body body_regs -> (0 _ : body_regs =%= regs) => Statement vars regs vars regs
while cond body = for nop cond nop body

-- Define with derived type and assign immediately
public export %inline
(?#=) : (n : Name) -> {ty : Type'} -> {0 regs : Registers rc} -> Expression ((n, ty)::vars) regs ty -> Statement vars regs ((n, ty)::vars) regs
n ?#= v = ty. n *> n #= v

namespace AlternativeDefineAndAssign

  public export %inline
  (!#=) : (p : (Name, Type')) -> Expression (p::vars) regs (snd p) -> Statement vars regs (p::vars) regs
  (n, _) !#= v = n ?#= v

  public export %inline
  (.) : a -> b -> (b, a)
  (.) a b = (b, a)

namespace ShowC

  Show Type' where
    show Bool'   = "bool"
    show Int'    = "int"
    show String' = "char *"

  isNopDeeply : Statement preV preR postV postR -> Bool
  isNopDeeply Statement.nop = True
  isNopDeeply (x *> y)      = isNopDeeply x && isNopDeeply y
  isNopDeeply _             = False

  ||| Next identation
  n : Nat -> Nat
  n = (+ 2)

  showInd : (indent : Nat) -> Statement preV preR postV postR -> String
  showInd i Statement.nop = ""
  showInd i (ty . n) = indent i $ show ty ++ " " ++ show n ++ ";"
  showInd i (Statement.(#=) n v) = indent i $ show n ++ " = " ++ show v ++ ";"
  showInd i (reg %= v) = indent i "[\{show $ finToNat reg}] = \{show v};"
  showInd i (for init cond upd body) = if isNopDeeply init -- TODO to add a situation when we can use normal C's `for`
                                         then showWhile i
                                         else indent i "{\n" ++
                                                showInd (n i) init ++ "\n" ++
                                                showWhile (n i) ++ "\n" ++
                                              indent i "}"
                                         where
                                           showWhile : Nat -> String
                                           showWhile i =
                                             indent i ("while (" ++ show cond ++ ") {\n") ++
                                               showInd (n i) body ++ "\n" ++
                                               (if isNopDeeply upd then ""
                                                 else showInd (n i) upd ++ "\n") ++
                                             indent i "}"
  showInd i (if__ cond x y) = indent i "if (" ++ show cond ++ ") {\n" ++
                                showInd (n i) x ++ "\n" ++
                              indent i "}" ++ if isNopDeeply y then ""
                                else " else {\n" ++
                                  showInd (n i) y ++ "\n" ++
                                  indent i "}"
  showInd i (x *> y) = if isNopDeeply x
                         then showInd i y
                         else showInd i x ++
                         if isNopDeeply y then "" else "\n" ++
                         showInd i y
  showInd i (block x) = indent i "{\n" ++ showInd (n i) x ++ "\n" ++ indent i "}"
  showInd i (print x) = indent i $ "puts(" ++ show x ++ ");"

  export
  Show (Statement preV preR postV postR) where
    show = showInd 0

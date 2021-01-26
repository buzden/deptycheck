module Example.Pil.Lang.Statement

import Data.List.Lookup

import Data.String.Extra

import Example.Pil.Lang.Common
import Example.Pil.Lang.Expression

%default total

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

namespace ShowC

  export
  Show Type' where
    show Bool'   = "bool"
    show Int'    = "int"
    show String' = "char *"

  isNopDeeply : Statement pre post -> Bool
  isNopDeeply Statement.nop = True
  isNopDeeply (x *> y)      = isNopDeeply x && isNopDeeply y
  isNopDeeply _             = False

  ||| Next identation
  n : Nat -> Nat
  n = (+ 2)

  showInd : (indent : Nat) -> Statement pre post -> String
  showInd i Statement.nop = ""
  showInd i (ty . n) = indent i $ show ty ++ " " ++ show n ++ ";"
  showInd i (Statement.(#=) n v) = indent i $ show n ++ " = " ++ show v ++ ";"
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
  Show (Statement pre post) where
    show = showInd 0

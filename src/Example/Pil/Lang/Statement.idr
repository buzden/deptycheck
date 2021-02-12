module Example.Pil.Lang.Statement

import Data.List.Lookup

import Data.String.Extra

import Example.Pil.Lang.Common
import Example.Pil.Lang.Expression

%default total

infix 2 #=, ?#=
infixr 1 *>

data Statement : (preV : Variables) -> (preR : Registers rc) -> (postV : Variables) -> (updR : RegisterTyUpdates rc) -> Type

public export %inline
0 (.varsAfter) : Statement preV preR postV updR -> Variables
stmt.varsAfter = postV

public export %inline
0 (.regsAfter) : {0 preR : Registers rc} -> Statement preV preR postV updR -> Registers rc
stmt.regsAfter = preR `withUpdates` updR

public export
data Statement : (preV : Variables) -> (preR : Registers rc) -> (postV : Variables) -> (updR : RegisterTyUpdates rc) -> Type where
  nop  : Statement vars vars
  (.)  : (ty : Type') -> (n : Name) -> Statement vars $ (n, ty)::vars
  (#=) : (n : Name) -> (0 lk : Lookup n vars) => (v : Expression vars lk.reveal) -> Statement vars vars
  for  : (init : Statement outer_vars inside_for)  -> (cond : Expression inside_for Bool') ->
         (upd  : Statement inside_for inside_for) -> (body : Statement inside_for after_body) ->
         Statement outer_vars outer_vars
  if__ : (cond : Expression vars Bool') -> Statement vars vars_then -> Statement vars vars_else -> Statement vars vars
  (*>) : Statement pre mid -> Statement mid post -> Statement pre post
  block : Statement outer inside -> Statement outer outer
  print : Show (idrTypeOf ty) => Expression vars ty -> Statement vars vars

public export %inline
(>>=) : Statement pre mid -> (Unit -> Statement mid post) -> Statement pre post
a >>= f = a *> f ()

public export %inline
if_  : (cond : Expression vars Bool') -> Statement vars vars_then -> Statement vars vars
if_ c t = if__ c t nop

public export %inline
while : Expression vars Bool' -> Statement vars after_body -> Statement vars vars
while cond = for nop cond nop

-- Define with derived type and assign immediately
public export %inline
(?#=) : (n : Name) -> {ty : Type'} -> Expression ((n, ty)::vars) ty -> Statement vars $ (n, ty)::vars
n ?#= v = ty. n *> n #= v

namespace AlternativeDefineAndAssign

  public export %inline
  (#=) : (p : (Name, Type')) -> Expression (p::vars) (snd p) -> Statement vars $ p::vars
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

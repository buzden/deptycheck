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
  nop  : Statement vars regs vars NoTyUpdates

  (.)  : (ty : Type') -> (n : Name) -> Statement vars regs ((n, ty)::vars) NoTyUpdates

  (#=) : (n : Name) -> (0 lk : Lookup n vars) => (v : Expression vars regs lk.reveal) -> Statement vars regs vars NoTyUpdates

  for  : (init : Statement preV preR insideV insideUpdR) ->
         (cond : Expression init.varsAfter init.regsAfter Bool') ->
         (upd  : Statement init.varsAfter init.regsAfter init.varsAfter NoTyUpdates) ->
         (body : Statement init.varsAfter init.regsAfter postBodyV NoTyUpdates) ->
         Statement preV preR preV insideUpdR
         -- Registers that are changed in `upd` or `body` must be unavailable in `cond`, `upd`, `body` and `for` itself
         -- in the case when we allow `upd` and `body` to change register types.

  if__ : (cond : Expression vars regs Bool') ->
         Statement vars regs varsThen regUpdThen ->
         Statement vars regs varsElse regUpdElse ->
         Statement vars regs vars $ threeWayMergeUpds regs regUpdThen regUpdElse

  (*>) : (l : Statement preV preR midV updR1) ->
         (r : Statement l.varsAfter l.regsAfter postV updR2) ->
         Statement preV preR postV $ updsSequential updR1 updR2

  block : Statement preV preR insideV updR -> Statement preV preR preV updR

  print : Show (idrTypeOf ty) => Expression vars regs ty -> Statement vars regs vars NoTyUpdates

public export %inline
(>>=) : (l : Statement preV preR midV updR1) -> (Unit -> Statement l.varsAfter l.regsAfter postV updR2) -> Statement preV preR postV $ updsSequential updR1 updR2
a >>= f = a *> f ()

public export %inline
if_  : (cond : Expression vars regs Bool') -> Statement vars regs varsThen updThen -> Statement vars regs vars $ undefUpds regs updThen
if_ c t = rewrite undefUpds_as_3wayMerge regs updThen in if__ c t nop

public export %inline
while : Expression vars regs Bool' -> Statement vars regs after_body NoTyUpdates -> Statement vars regs vars NoTyUpdates
while cond body = for nop (rewrite withUpdates_neutral regs in cond) nop (rewrite withUpdates_neutral regs in body)

-- Define with derived type and assign immediately
public export %inline
(?#=) : (n : Name) -> {ty : Type'} -> {0 regs : Registers rc} -> Expression ((n, ty)::vars) regs ty -> Statement vars regs ((n, ty)::vars) NoTyUpdates
n ?#= v = rewrite sym $ updsSequential_neutral_l {rc} NoTyUpdates in
          ty. n *> (rewrite withUpdates_neutral regs in n #= v)

namespace AlternativeDefineAndAssign

  public export %inline
  (#=) : (p : (Name, Type')) -> Expression (p::vars) regs (snd p) -> Statement vars regs (p::vars) NoTyUpdates
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

  isNopDeeply : Statement pre regs post upd -> Bool
  isNopDeeply Statement.nop = True
  isNopDeeply (x *> y)      = isNopDeeply x && isNopDeeply y
  isNopDeeply _             = False

  ||| Next identation
  n : Nat -> Nat
  n = (+ 2)

  showInd : (indent : Nat) -> Statement pre regs post upd -> String
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
  Show (Statement pre regs post upd) where
    show = showInd 0

module Language.PilFun

import Data.Maybe
import Data.List
import Data.List.Quantifiers

Name : Type
Name = String

data IsIn : Name -> List (Name, a) -> Type where
  MkIsIn : IsJust (lookup n xs) -> IsIn n xs

0 (.found) : IsIn {a} n xs -> a
(.found) $ MkIsIn _ with 0 (lookup n xs)
  _ | Just x = x

export infix 1 ==>

record FunSig where
  constructor (==>)
  From : List Type
  To   : Type

covering -- actually, all is total, but I don't want to bother with `assert_total` in types
data Expr : List (Name, FunSig) -> List (Name, Type) ->
            Type -> Type where

  C : (x : ty) -> Expr funs vars ty

  V : (n : Name) -> (0 lk : n `IsIn` vars) =>
      Expr funs vars lk.found

  F : (n : Name) -> (0 lk : n `IsIn` funs) =>
      All (Expr funs vars) lk.found.From ->
      Expr funs vars lk.found.To

export infix 2 #=

covering
data Stmts : (funs  : List (Name, FunSig)) ->
             (preV  : List (Name, Type)) ->
             (postV : List (Name, Type)) -> Type where

  (.)  : (ty : Type) -> (n : Name) ->
         Stmts funs vars ((n, ty)::vars)

  (#=) : (n : Name) -> (0 lk : n `IsIn` vars) =>
         (v : Expr funs vars lk.found) ->
         Stmts funs vars vars

  If   : (cond : Expr funs vars Bool) ->
         Stmts funs vars vThen -> Stmts funs vars vElse ->
         Stmts funs vars vars

  (>>) : Stmts funs preV midV  -> Stmts funs midV postV ->
         Stmts funs preV postV

StdF : List (Name, FunSig)
StdF = [ ("+" , [Int, Int] ==> Int)
       , ("<" , [Int, Int] ==> Bool)
       , ("++", [Int] ==> Int)
       , ("||", [Bool, Bool] ==> Bool) ]

covering
program : Stmts StdF [] ?
program = do
  Int. "x"
  "x" #= C 5
  Int. "y"; Bool. "res"
  "y" #= F "+" [V "x", C 1]
  If (F "<" [F "++" [V "x"], V "y"])
     (do "y" #= C 0; "res" #= C False)
     (do Int. "z"; "z" #= F "+" [V "x", V "y"]
         Bool. "b"; "b" #= F "<" [V "x", C 5]
         "res" #= F "||" [V "b", F "<" [V "z", C 6]])

failing "Mismatch between: Int and Bool"
  bad : Stmts StdF [] ?
  bad = do
    Int. "x"; "x" #= C 5
    Bool. "y"; "y" #= F "+" [V "x", C 1]

failing "Mismatch between: [] and [Int]"
  bad : Stmts StdF [] ?
  bad = do
    Int. "x"; "x" #= C 5
    Int. "y"; "y" #= F "+" [V "x"]

failing "Mismatch between: Bool and Int"
  bad : Stmts StdF [] ?
  bad = do
    Int. "x"; "x" #= C 5
    Int. "y"; "y" #= F "+" [C True, V "x"]

failing #"
    Can't find an implementation for IsIn "z" [("x", Int)]"#
  bad : Stmts StdF [] ?
  bad = do
    Int. "x"; "x" #= C 5
    "z" #= V "x"

failing #"
    Can't find an implementation for IsIn "z" [("x", Int)]"#
  bad : Stmts StdF [] ?
  bad = do
    Int. "x"
    "x" #= V "z"

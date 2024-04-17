module Language.PilFun

import Data.Nat
import Data.SnocList.Quantifiers

-- Types of this primitive imperative language
data Ty = Int' | Bool'

data Literal : Ty -> Type where
  I : Nat  -> Literal Int'
  B : Bool -> Literal Bool'

export infix 1 ==>

record FunSig where
  constructor (==>)
  From : SnocList Ty
  To   : Ty

data IndexIn : SnocList a -> Type where
  Here  : IndexIn $ sx :< x
  There : IndexIn sx -> IndexIn $ sx :< x

index : (sx : SnocList a) -> IndexIn sx -> a
index (_ :<x) Here      = x
index (sx:<_) (There i) = index sx i

namespace DSL

  -- The following definitions are only for DSL for indexation of vars and funs

  namespace Literals

    export
    fromInteger : Integer -> Literal Int'
    fromInteger = I . fromInteger

    export
    True, False : Literal Bool'
    True = B True
    False = B False

  namespace IndexIn

    public export
    natToIndexIn : (n : Nat) -> {sx : SnocList a} -> n `LT` length sx => IndexIn sx
    natToIndexIn 0     {sx=sx:<x}              = Here
    natToIndexIn (S k) {sx=sx:<x} @{LTESucc l} = There $ natToIndexIn k

    public export
    weakenLT : {n : _} -> n `LT` m -> n `LTE` m
    weakenLT {n=Z}   (LTESucc x) = LTEZero
    weakenLT {n=S n} (LTESucc x) = LTESucc $ weakenLT x

    public export
    reverseLTMinus : {m, n : Nat} -> n `LT` m => (m `minus` S n) `LT` m
    reverseLTMinus {n = Z} {m=S m} = rewrite minusZeroRight m in reflexive
    reverseLTMinus {m=S m} {n=S n} @{LTESucc xx} = LTESucc $ weakenLT reverseLTMinus

    public export
    fromInteger : {sx : SnocList a} -> (n : Integer) -> (cast n `LT` length sx) => {- (x >= the Integer 0 = True) =>-} IndexIn sx
    fromInteger n with (cast {to=Nat} n)
      _ | n' = natToIndexIn (length sx `minus` S n') @{reverseLTMinus}

Vars : Type
Vars = SnocList Ty

Funs : Type
Funs = SnocList FunSig

Var : Vars -> Type
Var = IndexIn

Fun : Funs -> Type
Fun = IndexIn

covering -- actually, all is total, but I don't want to bother with `assert_total` in types
data Expr : Funs -> Vars -> Ty -> Type where

  C : (x : Literal ty) -> Expr funs vars ty

  V : (n : Var vars) ->
      Expr funs vars $ index vars n

  F : (n : Fun funs) ->
      All (Expr funs vars) (index funs n).From ->
      Expr funs vars (index funs n).To

export infix 2 #=

covering
data Stmts : (funs  : Funs) ->
             (preV  : Vars) ->
             (postV : Vars) -> Type where

  NewV : (ty : Ty) ->
         Stmts funs vars $ vars :< ty

  (#=) : (n : Var vars) ->
         (v : Expr funs vars $ index vars n) ->
         Stmts funs vars vars

  If   : (cond : Expr funs vars Bool') ->
         Stmts funs vars vThen -> Stmts funs vars vElse ->
         Stmts funs vars vars

  (>>) : Stmts funs preV midV  -> Stmts funs midV postV ->
         Stmts funs preV postV

StdF : Funs
StdF = [< [< Int', Int'] ==> Int'    -- "+"
       ,  [< Int', Int'] ==> Bool'   -- "<"
       ,  [< Int'] ==> Int'          -- "++"
       ,  [< Bool', Bool'] ==> Bool' -- "||"
       ]
Plus, LT, Inc, Or : Fun StdF
Plus = 0; LT = 1; Inc = 2; Or = 3

covering
program : Stmts StdF [<] ?
program = do
  NewV Int' -- 0
  0 #= C 5
  NewV Int' -- 1
  NewV Bool' -- 2
  1 #= F Plus [< V 0, C 1]
  If (F LT [< F Inc [< V 0], V 1])
     (do 1 #= C 0
         2 #= C False)
     (do NewV Int' -- 3
         3 #= F Plus [< V 0, V 1]
         NewV Bool' -- 4
         4 #= F LT [< V 0, C 5]
         2 #= F Or [< V 4, F LT [< V 3, C 6]])

failing "Mismatch between: Int' and Bool'"
  bad : Stmts StdF [<] ?
  bad = do
    NewV Int' -- 0
    0 #= C 5
    NewV Bool' -- 1
    1 #= F Plus [< V 0, C 1]

failing "Mismatch between: [<] and [<Int']"
  bad : Stmts StdF [<] ?
  bad = do
    NewV Int' -- 0
    0 #= C 5
    NewV Int' -- 1
    1 #= F Plus [< V 0]

failing "Mismatch between: Bool' and Int'"
  bad : Stmts StdF [<] ?
  bad = do
    NewV Int' -- 0
    0 #= C 5
    NewV Int' -- 1
    1 #= F Plus [< C True, V 0]

failing #"Can't find an implementation for LTE 3 (length [<Int'])"#
  bad : Stmts StdF [<] ?
  bad = do
    NewV Int' -- 0
    0 #= C 5
    2 #= V 0

failing #"Can't find an implementation for LTE 3 (length [<Int'])"#
  bad : Stmts StdF [<] ?
  bad = do
    NewV Int' -- 0
    0 #= V 2

module Language.PilFun

import Data.Nat

import Decidable.Equality

-- Types of this primitive imperative language
public export
data Ty = Int' | Bool'

export
DecEq Ty where
  decEq Int' Int' = Yes Refl
  decEq Bool' Bool' = Yes Refl
  decEq Int' Bool' = No $ \case Refl impossible
  decEq Bool' Int' = No $ \case Refl impossible

public export
data Literal : Ty -> Type where
  I : Nat  -> Literal Int'
  B : Bool -> Literal Bool'

public export
data MaybeTy = Nothing | Just Ty

export
Injective PilFun.Just where injective Refl = Refl

export
DecEq MaybeTy where
  decEq Nothing Nothing = Yes Refl
  decEq (Just t) (Just t') = decEqCong (decEq t t')
  decEq Nothing (Just _) = No $ \case Refl impossible
  decEq (Just _) Nothing = No $ \case Refl impossible

namespace SnocListTy

  public export
  data SnocListTy : Type where
    Lin  : SnocListTy
    (:<) : SnocListTy -> Ty -> SnocListTy

  public export
  data IndexIn : SnocListTy -> Type where
    Here  : IndexIn $ sx :< x
    There : IndexIn sx -> IndexIn $ sx :< x

  public export
  index : (sx : SnocListTy) -> IndexIn sx -> Ty
  index (_ :<x) Here      = x
  index (sx:<_) (There i) = index sx i

  public export
  length : SnocListTy -> Nat
  length Lin = Z
  length (sx :< _) = S $ length sx

  export
  Biinjective SnocListTy.(:<) where
    biinjective Refl = (Refl, Refl)

  export
  DecEq SnocListTy where
    decEq [<] [<] = Yes Refl
    decEq (sx :< x) (sx' :< x') = decEqCong2 (decEq sx sx') (decEq x x')
    decEq [<] (_:<_) = No $ \case Refl impossible
    decEq (_:<_) [<] = No $ \case Refl impossible

  public export
  data AtIndex : (sx : SnocListTy) -> (idx : IndexIn sx) -> Ty -> Type where
    [search sx idx]
    Here'  : AtIndex (sx :< ty) Here ty
    There' : AtIndex sx i ty -> AtIndex (sx :< x) (There i) ty

  public export
  (++) : SnocListTy -> SnocListTy -> SnocListTy
  (++) sx Lin       = sx
  (++) sx (sy :< y) = (sx ++ sy) :< y

export infix 1 ==>

public export
record FunSig where
  constructor (==>)
  From : SnocListTy
  To   : MaybeTy

export
Biinjective (==>) where
  biinjective Refl = (Refl, Refl)

export
DecEq FunSig where
  decEq (f ==> t) (f' ==> t') = decEqCong2 (decEq f f') (decEq t t')

namespace SnocListFunSig

  public export
  data SnocListFunSig : Type where
    Lin  : SnocListFunSig
    (:<) : SnocListFunSig -> FunSig -> SnocListFunSig

  public export
  data IndexIn : SnocListFunSig -> Type where
    Here  : IndexIn $ sx :< x
    There : IndexIn sx -> IndexIn $ sx :< x

  public export
  index : (sx : SnocListFunSig) -> IndexIn sx -> FunSig
  index (_ :<x) Here      = x
  index (sx:<_) (There i) = index sx i

  public export
  length : SnocListFunSig -> Nat
  length Lin = Z
  length (sx :< _) = S $ length sx

  public export
  data AtIndex : (sx : SnocListFunSig) -> (idx : IndexIn sx) -> FunSig -> Type where
    [search sx idx]
    Here'  : AtIndex (sx :< sig) Here sig
    There' : AtIndex sx i sig -> AtIndex (sx :< x) (There i) sig

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

  namespace Utils

    public export
    weakenLT : {n : _} -> n `LT` m -> n `LTE` m
    weakenLT {n=Z}   (LTESucc x) = LTEZero
    weakenLT {n=S n} (LTESucc x) = LTESucc $ weakenLT x

    public export
    reverseLTMinus : {m, n : Nat} -> n `LT` m => (m `minus` S n) `LT` m
    reverseLTMinus {n = Z} {m=S m} = rewrite minusZeroRight m in reflexive
    reverseLTMinus {m=S m} {n=S n} @{LTESucc xx} = LTESucc $ weakenLT reverseLTMinus

  namespace SnocListTy.IndexIn

    public export
    natToIndexIn : (n : Nat) -> {sx : SnocListTy} -> n `LT` length sx => IndexIn sx
    natToIndexIn 0     {sx=sx:<x}              = Here
    natToIndexIn (S k) {sx=sx:<x} @{LTESucc l} = There $ natToIndexIn k

    public export
    fromInteger : {sx : SnocListTy} -> (n : Integer) -> (cast n `LT` length sx) => {- (x >= the Integer 0 = True) =>-} IndexIn sx
    fromInteger n with (cast {to=Nat} n)
      _ | n' = natToIndexIn (length sx `minus` S n') @{reverseLTMinus}

  namespace SnocListFunSig.IndexIn

    public export
    natToIndexIn : (n : Nat) -> {sx : SnocListFunSig} -> n `LT` length sx => IndexIn sx
    natToIndexIn 0     {sx=sx:<x}              = Here
    natToIndexIn (S k) {sx=sx:<x} @{LTESucc l} = There $ natToIndexIn k

    public export
    fromInteger : {sx : SnocListFunSig} -> (n : Integer) -> (cast n `LT` length sx) => {- (x >= the Integer 0 = True) =>-} IndexIn sx
    fromInteger n with (cast {to=Nat} n)
      _ | n' = natToIndexIn (length sx `minus` S n') @{reverseLTMinus}

public export
Vars : Type
Vars = SnocListTy

public export
Funs : Type
Funs = SnocListFunSig

public export
Var : Vars -> Type
Var = IndexIn

public export
Fun : Funs -> Type
Fun = IndexIn

public export
data Expr : Funs -> Vars -> Ty -> Type
public export
data ExprsSnocList : Funs -> Vars -> SnocListTy -> Type

data Expr : Funs -> Vars -> Ty -> Type where

  C : (x : Literal ty) -> Expr funs vars ty

  V : (n : Var vars) ->
      AtIndex vars n ty =>
      Expr funs vars ty

  F : (n : Fun funs) ->
      AtIndex funs n (from ==> Just to) =>
      ExprsSnocList funs vars from ->
      Expr funs vars to

data ExprsSnocList : Funs -> Vars -> SnocListTy -> Type where
  Lin  : ExprsSnocList funs vars [<]
  (:<) : ExprsSnocList funs vars sx -> Expr funs vars ty -> ExprsSnocList funs vars (sx :< ty)

export infix 2 #=

public export
data Stmts : (funs : Funs) ->
             (vars : Vars) ->
             (maxFunDepth : Nat) ->
             (retTy : MaybeTy) -> Type where

  NewV : (ty : Ty) ->
         (cont : Stmts funs (vars :< ty) mfd retTy) ->
         Stmts funs vars mfd retTy

  NewF : (sig : FunSig) ->
         (body : Stmts funs (vars ++ sig.From) mfd sig.To) ->
         (cont : Stmts (funs :< sig) vars (S mfd) retTy) ->
         Stmts funs vars (S mfd) retTy

  (#=) : (n : Var vars) ->
         (v : Expr funs vars $ index vars n) ->
         (cont : Stmts funs vars mfd retTy) ->
         Stmts funs vars mfd retTy

  If   : (cond : Expr funs vars Bool') ->
         (th, el : Stmts funs vars mfd Nothing) -> -- we assume that we don't return from inside `if`
         (cont : Stmts funs vars mfd retTy) ->
         Stmts funs vars mfd retTy

  Call : (n : Fun funs) ->
         AtIndex funs n (from ==> Nothing) =>
         ExprsSnocList funs vars from ->
         (cont : Stmts funs vars mfd retTy) ->
         Stmts funs vars mfd retTy

  Ret  : Expr funs vars retTy -> Stmts funs vars mfd $ Just retTy

  Nop  : Stmts funs vars mfd Nothing

(>>) : (Stmts f' v' mfd' rt' -> Stmts f v mfd rt) -> Stmts f' v' mfd' rt' -> Stmts f v mfd rt
(>>) = id

StdF : Funs
StdF = [< [< Int', Int'] ==> Just Int'    -- "+"
       ,  [< Int', Int'] ==> Just Bool'   -- "<"
       ,  [< Int'] ==> Just Int'          -- "++"
       ,  [< Bool', Bool'] ==> Just Bool' -- "||"
       ,  [< Int' ] ==> Nothing           -- printf for ints
       ]
Plus, LT, Inc, Or : Fun StdF
Plus = 0; LT = 1; Inc = 2; Or = 3
Print : Fun StdF
Print = 4

program : Stmts StdF [<] 0 Nothing
program = do
  NewV Int' -- 0
  0 #= C 5
  NewV Int' -- 1
  NewV Bool' -- 2
  1 #= F Plus [< V 0, C 1]
  If (F LT [< F Inc [< V 0], V 1])
     (do 1 #= C 0
         2 #= C False
         Nop)
     (do NewV Int' -- 3
         3 #= F Plus [< V 0, V 1]
         NewV Bool' -- 4
         4 #= F LT [< V 0, C 5]
         2 #= F Or [< V 4, F LT [< V 3, C 6]]
         Nop)
  Call Print [< V 1]
  Nop

failing -- "Mismatch between: Int' and Bool'"
  bad : Stmts StdF [<] 0 Nothing
  bad = do
    NewV Int' -- 0
    0 #= C 5
    NewV Bool' -- 1
    1 #= F Plus [< V 0, C 1]
    Nop

failing -- "Mismatch between: [<] and [<Int']"
  bad : Stmts StdF [<] 0 Nothing
  bad = do
    NewV Int' -- 0
    0 #= C 5
    NewV Int' -- 1
    1 #= F Plus [< V 0]
    Nop

failing -- "Mismatch between: Bool' and Int'"
  bad : Stmts StdF [<] 0 Nothing
  bad = do
    NewV Int' -- 0
    0 #= C 5
    NewV Int' -- 1
    1 #= F Plus [< C True, V 0]
    Nop

failing #"Can't find an implementation for LTE 3 (length [<Int'])"#
  bad : Stmts StdF [<] 0 Nothing
  bad = do
    NewV Int' -- 0
    0 #= C 5
    2 #= V 0
    Nop

failing #"Can't find an implementation for LTE 3 (length [<Int'])"#
  bad : Stmts StdF [<] 0 Nothing
  bad = do
    NewV Int' -- 0
    0 #= V 2
    Nop

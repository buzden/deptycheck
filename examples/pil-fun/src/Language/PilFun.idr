module Language.PilFun

import public Data.Fuel
import public Data.Nat

import Decidable.Equality

import Test.DepTyCheck.Gen

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

  public export %inline
  (.length) : SnocListTy -> Nat
  (.length) = length

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

  public export %inline
  (.length) : SnocListFunSig -> Nat
  (.length) = length

  public export
  data AtIndex : (sx : SnocListFunSig) -> (idx : IndexIn sx) -> FunSig -> Type where
    [search sx idx]
    Here'  : AtIndex (sx :< sig) Here sig
    There' : AtIndex sx i sig -> AtIndex (sx :< x) (There i) sig

public export
Vars : Type
Vars = SnocListTy

public export
Funs : Type
Funs = SnocListFunSig

public export
data ExprsSnocList : Funs -> Vars -> SnocListTy -> Type

public export
data Expr : Funs -> Vars -> Ty -> Type where

  C : (x : Literal ty) -> Expr funs vars ty

  V : (n : IndexIn vars) ->
      AtIndex vars n ty =>
      Expr funs vars ty

  F : (n : IndexIn funs) ->
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
             (retTy : MaybeTy) -> Type where

  NewV : (ty : Ty) ->
         (initial : Expr funs vars ty) ->
         (cont : Stmts funs (vars :< ty) retTy) ->
         Stmts funs vars retTy

  NewF : (sig : FunSig) ->
         (body : Stmts funs (vars ++ sig.From) sig.To) ->
         (cont : Stmts (funs :< sig) vars retTy) ->
         Stmts funs vars retTy

  (#=) : (n : IndexIn vars) ->
         (v : Expr funs vars $ index vars n) ->
         (cont : Stmts funs vars retTy) ->
         Stmts funs vars retTy

  If   : (cond : Expr funs vars Bool') ->
         (th, el : Stmts funs vars Nothing) -> -- we assume that we don't return from inside `if`
         (cont : Stmts funs vars retTy) ->
         Stmts funs vars retTy

  Call : (n : IndexIn funs) ->
         AtIndex funs n (from ==> Nothing) =>
         ExprsSnocList funs vars from ->
         (cont : Stmts funs vars retTy) ->
         Stmts funs vars retTy

  Ret  : Expr funs vars retTy -> Stmts funs vars $ Just retTy

  Nop  : Stmts funs vars Nothing

export
genStmts : Fuel -> (funs : Funs) -> (vars : Vars) -> (retTy : MaybeTy) -> Gen MaybeEmpty $ Stmts funs vars retTy

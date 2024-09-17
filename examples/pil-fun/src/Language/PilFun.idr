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

public export
data Mut = Mutable | Immutable

export
DecEq Mut where
  decEq Mutable   Mutable   = Yes Refl
  decEq Immutable Immutable = Yes Refl
  decEq Mutable   Immutable = No $ \case Refl impossible
  decEq Immutable Mutable   = No $ \case Refl impossible

namespace SnocListTy

  public export
  data SnocListTy : Type where
    Lin  : SnocListTy
    (:<) : SnocListTy -> Ty -> SnocListTy

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

namespace SnocListTyMut

  public export
  data SnocListTyMut : Type where
    Lin  : SnocListTyMut
    (:<) : SnocListTyMut -> Ty -> Mut -> SnocListTyMut

  public export
  data IndexIn : SnocListTyMut -> Type where
    Here  : IndexIn $ (:<) sx x mut
    There : IndexIn sx -> IndexIn $ (:<) sx x mut

  public export
  index : (sx : SnocListTyMut) -> IndexIn sx -> (Ty, Mut)
  index ((:<) _  x m) Here      = (x, m)
  index ((:<) sx _ _) (There i) = index sx i

  public export
  length : SnocListTyMut -> Nat
  length Lin = Z
  length ((:<) sx _ _) = S $ length sx

  public export %inline
  (.length) : SnocListTyMut -> Nat
  (.length) = length

  export
  DecEq SnocListTyMut where
    decEq [<] [<] = Yes Refl
    decEq ((:<) sx x m) ((:<) sx' x' m') with (decEq sx sx')
      _                                   | No nsx = No $ \case Refl => nsx Refl
      decEq ((:<) sx x m) ((:<) sx x' m') | Yes Refl with (decEq x x')
        _                                             | No nx = No $ \case Refl => nx Refl
        decEq ((:<) sx x m) ((:<) sx x m') | Yes Refl | Yes Refl with (decEq m m')
          _                                                       | No mx = No $ \case Refl => mx Refl
          decEq ((:<) sx x m) ((:<) sx x m) | Yes Refl | Yes Refl | Yes Refl = Yes Refl
    decEq [<] ((:<) _ _ _) = No $ \case Refl impossible
    decEq ((:<) _ _ _) [<] = No $ \case Refl impossible

  public export
  data AtIndex : {sx : SnocListTyMut} -> (idx : IndexIn sx) -> Ty -> Mut -> Type where
    [search sx idx]
    Here'  : AtIndex {sx = (:<) sx ty mut} Here ty mut
    There' : AtIndex {sx} i ty mut -> AtIndex {sx = (:<) sx x m} (There i) ty mut

  ||| Add a bunch of immutable variables
  public export
  (++) : SnocListTyMut -> SnocListTy -> SnocListTyMut
  (++) sx Lin       = sx
  (++) sx (sy :< y) = (:<) (sx ++ sy) y Immutable

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
  data AtIndex : {sx : SnocListFunSig} -> (idx : IndexIn sx) -> FunSig -> Type where
    [search sx idx]
    Here'  : AtIndex {sx = sx :< sig} Here sig
    There' : AtIndex {sx} i sig -> AtIndex {sx = sx :< x} (There i) sig

public export
Vars : Type
Vars = SnocListTyMut

public export
Funs : Type
Funs = SnocListFunSig

public export
data ExprsSnocList : Funs -> Vars -> SnocListTy -> Type

public export
data Expr : Funs -> Vars -> Ty -> Type where

  C : (x : Literal ty) -> Expr funs vars ty

  V : (n : IndexIn vars) ->
      AtIndex n ty mut =>
      Expr funs vars ty

  F : (n : IndexIn funs) ->
      AtIndex n (from ==> Just to) =>
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
         (mut : Mut) ->
         (initial : Expr funs vars ty) ->
         (cont : Stmts funs ((:<) vars ty mut) retTy) ->
         Stmts funs vars retTy

  NewF : (sig : FunSig) ->
         (body : Stmts funs (vars ++ sig.From) sig.To) ->
         (cont : Stmts (funs :< sig) vars retTy) ->
         Stmts funs vars retTy

  (#=) : (n : IndexIn vars) ->
         AtIndex n ty Mutable =>
         (v : Expr funs vars ty) ->
         (cont : Stmts funs vars retTy) ->
         Stmts funs vars retTy

  If   : (cond : Expr funs vars Bool') ->
         (th, el : Stmts funs vars Nothing) -> -- we assume that we don't return from inside `if`
         (cont : Stmts funs vars retTy) ->
         Stmts funs vars retTy

  Call : (n : IndexIn funs) ->
         AtIndex n (from ==> Nothing) =>
         ExprsSnocList funs vars from ->
         (cont : Stmts funs vars retTy) ->
         Stmts funs vars retTy

  Ret  : Expr funs vars retTy -> Stmts funs vars $ Just retTy

  Nop  : Stmts funs vars Nothing

export
genStmts : Fuel -> (funs : Funs) -> (vars : Vars) -> (retTy : MaybeTy) -> Gen MaybeEmpty $ Stmts funs vars retTy

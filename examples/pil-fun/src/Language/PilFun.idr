module Language.PilFun

import public Data.Fuel
import public Data.Nat
import public Data.SnocList
import public Data.SnocList.Quantifiers

import Decidable.Equality

import Test.DepTyCheck.Gen

%default total

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
data Mut = Mutable | Immutable

export
DecEq Mut where
  decEq Mutable   Mutable   = Yes Refl
  decEq Immutable Immutable = Yes Refl
  decEq Mutable   Immutable = No $ \case Refl impossible
  decEq Immutable Mutable   = No $ \case Refl impossible

namespace SnocListTyMut

  public export
  data IndexIn : SnocList t -> Type where
    Here  : IndexIn $ (:<) sx x
    There : IndexIn sx -> IndexIn $ (:<) sx x

  public export
  index : (sx : SnocList t) -> IndexIn sx -> t
  index ((:<) _ x) Here      = x
  index ((:<) sx _) (There i) = index sx i

  public export %inline
  (.length) : SnocList _ -> Nat
  (.length) = length

  public export
  data AtIndex : {sx : SnocList t} -> (idx : IndexIn sx) -> t -> Type where
    [search sx idx]
    Here'  : AtIndex {sx = (:<) sx tm} Here tm
    There' : AtIndex {sx} i rm -> AtIndex {sx = (:<) sx x} (There i) rm

  ||| Add a bunch of immutable variables
  public export
  (++) : SnocList (Ty, Mut) -> SnocList Ty -> SnocList (Ty, Mut)
  (++) sx Lin       = sx
  (++) sx (sy :< y) = (:<) (sx ++ sy) (y, Immutable)

export infix 1 ==>

public export
record FunSig where
  constructor (==>)
  From : SnocList Ty
  To   : Maybe Ty

export
Biinjective (==>) where
  biinjective Refl = (Refl, Refl)

export
DecEq FunSig where
  decEq (f ==> t) (f' ==> t') = decEqCong2 (decEq f f') (decEq t t')

public export
Vars : Type
Vars = SnocList (Ty, Mut)

public export
Funs : Type
Funs = SnocList FunSig

public export
data ExprsSnocList : Funs -> Vars -> SnocList Ty -> Type

public export
data Expr : Funs -> Vars -> Ty -> Type where

  C : (x : Literal ty) -> Expr funs vars ty

  V : {mut : Mut} ->
      (n : IndexIn vars) ->
      AtIndex n (ty, mut) =>
      Expr funs vars ty

  F : (n : IndexIn funs) ->
      {from : _} ->
      {to : _} ->
      AtIndex n (from ==> Just to) =>
      ExprsSnocList funs vars from ->
      Expr funs vars to

data ExprsSnocList : Funs -> Vars -> SnocList Ty -> Type where
  Lin  : ExprsSnocList funs vars [<]
  (:<) : ExprsSnocList funs vars sx -> Expr funs vars ty -> ExprsSnocList funs vars (sx :< ty)

export infix 2 #=

public export
data Stmts : (funs : Funs) ->
             (vars : Vars) ->
             (retTy : Maybe Ty) -> Type where

  NewV : (ty : Ty) ->
         (mut : Mut) ->
         (initial : Expr funs vars ty) ->
         (cont : Stmts funs ((:<) vars (ty, mut)) retTy) ->
         Stmts funs vars retTy

  NewF : (sig : FunSig) ->
         (body : Stmts funs (vars ++ sig.From) sig.To) ->
         (cont : Stmts (funs :< sig) vars retTy) ->
         Stmts funs vars retTy

  (#=) : (n : IndexIn vars) ->
         AtIndex n (ty, Mutable) =>
         (v : Expr funs vars ty) ->
         (cont : Stmts funs vars retTy) ->
         Stmts funs vars retTy

  If   : (cond : Expr funs vars Bool') ->
         (th, el : Stmts funs vars Nothing) -> -- we assume that we don't return from inside `if`
         (cont : Stmts funs vars retTy) ->
         Stmts funs vars retTy

  Call : (n : IndexIn funs) ->
         {from : _} ->
         AtIndex n (from ==> Nothing) =>
         ExprsSnocList funs vars from ->
         (cont : Stmts funs vars retTy) ->
         Stmts funs vars retTy

  Ret  : Expr funs vars retTy -> Stmts funs vars $ Just retTy

  Nop  : Stmts funs vars Nothing

export
genStmts : Fuel -> (funs : Funs) -> (vars : Vars) -> (retTy : Maybe Ty) -> Gen MaybeEmpty $ Stmts funs vars retTy

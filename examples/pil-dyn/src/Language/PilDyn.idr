module Language.PilDyn

import public Data.Fin
import Data.String

import Decidable.Equality

%default total

-------------------------
--- Types and context ---
-------------------------

public export
data Ty = I | B

export
DecEq Ty where
  decEq I I = Yes Refl
  decEq B B = Yes Refl
  decEq I B = No $ \Refl impossible
  decEq B I = No $ \Refl impossible

public export
data MaybeTy = Nothing | Just Ty

export
Injective PilDyn.Just where
  injective Refl = Refl

export
DecEq MaybeTy where
  decEq Nothing Nothing = Yes Refl
  decEq (Just x) (Just y) = decEqCong $ decEq x y
  decEq Nothing (Just _) = No $ \Refl impossible
  decEq (Just _) Nothing = No $ \Refl impossible

public export
data Literal : Ty -> Type where
  IntVal  : Int32 -> Literal I
  BoolVal : Bool -> Literal B

namespace Regs
  public export
  data Regs : Nat -> Type where
    Nil  : Regs 0
    (::) : MaybeTy -> Regs n -> Regs $ S n

export
Biinjective Regs.(::) where
  biinjective Refl = (Refl, Refl)

export
DecEq (Regs n) where
  decEq [] [] = Yes Refl
  decEq (x::xs) (y::ys) = decEqCong2 (decEq x y) (decEq xs ys)

public export
update : Fin r -> MaybeTy -> Regs r -> Regs r
update FZ     t (x::xs) = t :: xs
update (FS i) t (x::xs) = x :: update i t xs

public export
data RegIsType : Fin r -> Ty -> Regs r -> Type where
  Here  : RegIsType FZ t (Just t :: rest)
  There : RegIsType i t rest -> RegIsType (FS i) t (reg :: rest)

-------------------
--- Expressions ---
-------------------

public export
data BinOp : Ty -> Ty -> Ty -> Type where
  Add : BinOp I I I
  Mul : BinOp I I I

  Eq  : BinOp a a B

  LT  : BinOp I I B
  LTE : BinOp I I B

  And : BinOp B B B
  Or  : BinOp B B B
  Xor : BinOp B B B

precBin : BinOp l r t -> Prec
precBin Add = User 8
precBin Mul = User 9
precBin Eq  = User 6
precBin LT  = User 6
precBin LTE = User 6
precBin And = User 5
precBin Or  = User 4
precBin Xor = User 6

public export
data UnOp : Ty -> Ty -> Type where
  Minus : UnOp I I

  Not : UnOp B B

precUn : UnOp r t -> Prec
precUn Minus = PrefixMinus
precUn Not   = User 7

public export
data Expr : (maxDepth : Nat) -> Regs r -> Ty -> Type where

  Lit : Literal t -> Expr _ regs t

  Read : (idx : Fin r) -> RegIsType idx t regs => Expr _ regs t

  Binary : Expr d regs l -> BinOp l r t -> Expr d regs r -> Expr (S d) regs t

  Unary : UnOp r t -> Expr d regs r -> Expr (S d) regs t

---------------------
--- Linear blocks ---
---------------------

public export
data ReducesTo : (ins, outs : Regs r) -> Type where
  II : ReducesTo [] []
  JJ : ReducesTo rs rs' -> ReducesTo (Just t :: rs) (Just t :: rs')
  JN : ReducesTo rs rs' -> ReducesTo (Just t :: rs) (Nothing :: rs')

public export
data LinBlock : (ins, outs : Regs r) -> Type where

  End : ReducesTo ins outs => LinBlock ins outs

  Assign : (target : Fin r) ->
           (expr : Expr 2 ins t) ->
           (cont : LinBlock (update target (Just t) ins) outs) ->
           LinBlock ins outs

--- Linear block DSL ---

public export
data Assignment : (target : _) -> (ins : _) -> (t : _) -> Type where
  (#=) : (target : Fin r) -> Expr 2 ins t -> Assignment target ins t

export infix 2 #=

public export %inline
(>>) : Assignment target ins t -> LinBlock (update target (Just t) ins) outs -> LinBlock ins outs
target #= expr >> cont = Assign target expr cont

export
fromInteger : (x : Integer) -> Expr d regs I
fromInteger = Lit . IntVal . cast

export
True, False : Expr d regs B
True  = Lit $ BoolVal True
False = Lit $ BoolVal False

-----------------------
--- Pretty-printing ---
-----------------------

export
Interpolation Ty where
  interpolate I = "I"
  interpolate B = "B"

export
Interpolation MaybeTy where
  interpolate $ Just t = "\{t}"
  interpolate Nothing  = "?"

export
Interpolation (Regs r) where
  interpolate = joinBy ", " . toList where
    toList : forall r. Regs r -> List String
    toList []      = []
    toList (x::xs) = interpolate x :: toList xs

export
Interpolation (Literal t) where
  interpolate $ IntVal i = show i
  interpolate $ BoolVal True  = "T"
  interpolate $ BoolVal False = "F"

export
Interpolation (BinOp l r t) where
  interpolate Add = "+"
  interpolate Mul = "*"
  interpolate Eq  = "=="
  interpolate LT  = "<"
  interpolate LTE = "<="
  interpolate And = "&&"
  interpolate Or  = "||"
  interpolate Xor = "^"

export
Interpolation (UnOp r t) where
  interpolate Minus = "-"
  interpolate Not   = "!"

Interpolation (Fin n) where
  interpolate idx = "[\{show idx}]"

Show (Expr d regs ty) where
  showPrec _ $ Lit l    = "\{l}"
  showPrec _ $ Read idx = "\{idx}"
  showPrec d $ Binary l op r = let d' = precBin op in showParens (d >= d') "\{showPrec d' l} \{op} \{showPrec d' r}"
  showPrec d $ Unary op e = let d' = precUn op in showParens (d >= d') "\{op}\{showPrec d' e}"

export
Interpolation (Expr d regs ty) where
  interpolate = show

export
Interpolation (LinBlock ins outs) where
  interpolate End = ""
  interpolate $ Assign target expr cont = """
    \{target} := \{expr}
    \{cont}
    """

export
Interpolation (ins ** LinBlock ins outs) where
  interpolate (ins ** lb) = """
    -- inputs: \{ins}
    \{lb}
    """

export
Interpolation (outs ** LinBlock ins outs) where
  interpolate (outs ** lb) = """
    -- outputs: \{outs}
    \{lb}
    """

export
Interpolation (ins ** outs ** LinBlock ins outs) where
  interpolate (ins ** outs ** lb) = """
    -- inputs:  \{ins}
    -- outputs: \{outs}
    \{lb}
    """

-- For `pick`ing
export
Interpolation a => Interpolation (Maybe a) where
  interpolate Nothing = "<nothing>"
  interpolate (Just x) = interpolate x

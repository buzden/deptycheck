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
data SimpleExpr : Regs r -> Ty -> Type where
  IntVal  : Int32 -> SimpleExpr regs I
  BoolVal : Bool -> SimpleExpr regs B
  Read    : (idx : Fin r) -> RegIsType idx t regs => SimpleExpr regs t

namespace BinOp

  public export
  data BinOp : (resTy : Ty) -> Type where
    Add : BinOp I
    Mul : BinOp I
    EqI : BinOp B
    LT  : BinOp B
    EqB : BinOp B
    And : BinOp B
    Or  : BinOp B

  public export
  record TyTy where
    constructor MkTyTy
    leftTy, rightTy : Ty

  public export
  (.binOpType) : BinOp resTy -> TyTy
  (.binOpType) Add = MkTyTy I I
  (.binOpType) Mul = MkTyTy I I
  (.binOpType) EqI = MkTyTy I I
  (.binOpType) LT  = MkTyTy I I
  (.binOpType) EqB = MkTyTy B B
  (.binOpType) And = MkTyTy B B
  (.binOpType) Or  = MkTyTy B B

public export
data Expr : Regs r -> Ty -> Type where
  Simple : SimpleExpr regs t -> Expr regs t
  Binary : (op : BinOp t) -> SimpleExpr regs op.binOpType.leftTy -> SimpleExpr regs op.binOpType.rightTy -> Expr regs t

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
           (expr : Expr ins t) ->
           (cont : LinBlock (update target (Just t) ins) outs) ->
           LinBlock ins outs

--- Linear block DSL ---

public export
data Assignment : (target : _) -> (ins : _) -> (t : _) -> Type where
  (#=) : (target : Fin r) -> Expr ins t -> Assignment target ins t

export infix 2 #=

public export %inline
(>>) : Assignment target ins t -> LinBlock (update target (Just t) ins) outs -> LinBlock ins outs
target #= expr >> cont = Assign target expr cont

export
fromInteger : (x : Integer) -> SimpleExpr regs I
fromInteger = IntVal . cast

export
True, False : SimpleExpr regs B
True  = BoolVal True
False = BoolVal False

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
Interpolation (BinOp t) where
  interpolate Add = "+"
  interpolate Mul = "*"
  interpolate EqI = "=="
  interpolate LT  = "<"
  interpolate EqB = "=="
  interpolate And = "&&"
  interpolate Or  = "||"

Interpolation (Fin n) where
  interpolate idx = "[\{show idx}]"

export
Interpolation (SimpleExpr regs ty) where
  interpolate $ IntVal i = show i
  interpolate $ BoolVal True  = "T"
  interpolate $ BoolVal False = "F"
  interpolate $ Read idx = "\{idx}"

export
Interpolation (Expr regs ty) where
  interpolate $ Simple e = "\{e}"
  interpolate $ Binary Mul (IntVal (-1)) r = "-\{r}"
  interpolate $ Binary Mul l (IntVal (-1)) = "-\{l}"
  interpolate $ Binary EqB (BoolVal False) r = "!\{r}"
  interpolate $ Binary EqB l (BoolVal False) = "!\{l}"
  interpolate $ Binary op l r = "\{l} \{op} \{r}"

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

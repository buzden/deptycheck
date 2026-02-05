module Example.Pil.Lang.Expression

import Data.List.Lookup
import Data.Maybe

import public Example.Pil.Lang.Aspects.Variables
import public Example.Pil.Lang.Aspects.Registers

%default total

public export
record Ops where
  constructor MkOps
  unary  : List (Type', String, Type')
  binary : List (Type', String, Type', Type')

public export
data Expression : Ops -> (vars : Variables) -> (regs : Registers rc) -> (res : Type') -> Type where
  -- Constant expression
  C' : {ty : Type'} -> (x : idrTypeOf ty) -> Expression ops vars regs ty

  -- Value of the variable
  V : (n : Name) -> (0 lk : Lookup n vars) => Expression ops vars regs lk.reveal

  -- Value of the register
  R : (r : Fin rc) -> (0 _ : IsJust $ index r regs) => Expression ops vars regs $ fromJust $ index r regs

  -- Unary operation over the result of another expression
  U : (lk : Lookup res ops.unary) =>
      Expression ops vars regs (snd lk.reveal) -> Expression ops vars regs res

  -- Binary operation over the results of two another expressions
  B : (lk : Lookup res ops.binary) =>
      Expression ops vars regs (fst $ snd lk.reveal) -> Expression ops vars regs (snd $ snd lk.reveal) -> Expression ops vars regs res

namespace Int

  public export %inline
  C : Int -> Expression ops vars regs Int'
  C x = C' x

namespace Bool

  public export %inline
  C : Bool -> Expression ops vars regs Bool'
  C x = C' x

namespace String

  public export %inline
  C : String -> Expression ops vars regs String'
  C x = C' x

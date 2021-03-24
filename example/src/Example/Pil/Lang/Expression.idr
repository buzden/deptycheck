module Example.Pil.Lang.Expression

import Data.List.Lookup
import Data.Maybe

import public Example.Pil.Lang.Aspects.Variables
import public Example.Pil.Lang.Aspects.Registers

%default total

public export
data Expression : (vars : Variables) -> (regs : Registers rc) -> (res : Type') -> Type where
  -- Constant expression
  C : {ty : Type'} -> (x : idrTypeOf ty) -> Expression vars regs ty

  -- Value of the variable
  V : (n : Name) -> (0 lk : Lookup n vars) => Expression vars regs lk.reveal

  -- Value of the register
  R : (r : Fin rc) -> (0 _ : IsJust $ index r regs) => Expression vars regs $ fromJust $ index r regs

  -- Unary operation over the result of another expression
  U : {default "?func" opName : String} ->
      (f : idrTypeOf a -> idrTypeOf b) ->
      Expression vars regs a -> Expression vars regs b

  -- Binary operation over the results of two another expressions
  B : {default "??" opName : String} ->
      (f : idrTypeOf a -> idrTypeOf b -> idrTypeOf c) ->
      Expression vars regs a -> Expression vars regs b -> Expression vars regs c

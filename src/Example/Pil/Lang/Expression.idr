module Example.Pil.Lang.Expression

import Data.List.Lookup

import Example.Pil.Lang.Common

%default total

public export
data Expression : (vars : Variables) -> (res : Type') -> Type where
  -- Constant expression
  C : {ty : Type'} -> (x : idrTypeOf ty) -> Expression vars ty
  -- Value of the variable
  V : (n : Name) -> (0 lk : Lookup n vars) => Expression vars lk.reveal
  -- Unary operation over the result of another expression
  U : {default "?func" opName : String} -> (f : idrTypeOf a -> idrTypeOf b) -> Expression vars a -> Expression vars b
  -- Binary operation over the results of two another expressions
  B : {default "??" opName : String} -> (f : idrTypeOf a -> idrTypeOf b -> idrTypeOf c) -> Expression vars a -> Expression vars b -> Expression vars c

namespace ShowC

  looksLikeInfixOperator : String -> Bool
  looksLikeInfixOperator =
    flip elem ["+", "-", "*", "/", "%", "==", "!=", "<", ">", ">=", "<=", "&&", "||", "&", "|", "^", "<<", ">>"]

  makeFuncName : String -> String
  makeFuncName = pack . map (\k => if isAlphaNum k then k else '_') . unpack

  export
  Show (Expression vars a) where
    show (C {ty=Bool'}   x) = show x
    show (C {ty=Int'}    x) = show x
    show (C {ty=String'} x) = show x
    show (V n)              = show n
    show (U {opName} _ e)   = opName ++ "(" ++ show e ++ ")"
    show (B {opName} _ l r) = if looksLikeInfixOperator opName
        then wr l ++ " " ++ opName ++ " " ++ wr r
        else makeFuncName opName ++ "(" ++ show l ++ ", " ++ show r ++ ")"
      where
      wr : Expression vars x -> String
      wr e@(B _ _ _) = "(" ++ show e ++ ")"
      wr e           = show e

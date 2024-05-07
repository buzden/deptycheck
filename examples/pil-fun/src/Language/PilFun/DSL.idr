module Language.PilFun.DSL

import public Language.PilFun

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

public export %inline
(>>) : (Stmts f' v' rt' -> Stmts f v rt) -> Stmts f' v' rt' -> Stmts f v rt
(>>) = id

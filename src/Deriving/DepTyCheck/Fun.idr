module Deriving.DepTyCheck.Fun

import public Data.Fuel

import Deriving.DepTyCheck.Gen

import public System.Random.Pure.StdGen

%default total

public export
0 HoldingM, (<--|) : (mty : Type) -> (0 _ : mty = Maybe ty) => (ty -> Type) -> Type
HoldingM x _ = x
(<--|) = HoldingM

export infixl 0 `HoldingM`, <--|

-- TODO to have typebind infix `WithM` analogue of `HoldingM` as soon as compiler support such signatures for typebinds (#3552).
-- TODO to have non-maybe infixl `Holding` and typebind infix `With` as soon as we can derive non-empty generators.
-- TODO to check that these approaches are not used together, as soon as the rest is implemented.

data Sum : (a, b, r : Nat) -> Type

f'' : (a, b : Nat) -> Maybe Nat <--| Sum a b <--| (`LT` 5)

genTargetByFunTarget : TTImp -> TTImp

export
deriveFunExpr : RandomGen g => (seed : g) -> (maxAttempts : Nat) -> (fuel : Fuel) -> (signature : TTImp) -> Elab TTImp
deriveFunExpr seed maxAttempts fuel funSig = do
  let (args, funTarget) = unPi funSig
  let genSig = piAll `(Test.DepTyCheck.Gen.Gen MaybeEmpty ~(genTargetByFunTarget funTarget)) (arg `(Data.Fuel.Fuel) :: args)
  ?deriveFunExpr_rhs

public export
0 FunDerivationDefaults : Type -> Type
FunDerivationDefaults ty = {default someStdGen seed : _} ->
                           {default 1000 maxAttempts : Nat} ->
                           {default (limit 100) fuel : Fuel} ->
                           ty

export %macro
deriveFun : FunDerivationDefaults $ Elab a
deriveFun = do
  Just signature <- goal
     | Nothing => fail "The goal signature is not found. Functions derivation must be used only for fully defined signatures"
  deriveFunExpr seed maxAttempts fuel signature >>= check

export %macro
deriveFunFor : FunDerivationDefaults $ (0 a : Type) -> Elab a
deriveFunFor ty = quote ty >>= deriveFunExpr seed maxAttempts fuel >>= check

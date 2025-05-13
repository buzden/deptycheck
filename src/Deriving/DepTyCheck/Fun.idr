module Deriving.DepTyCheck.Fun

import public Data.Fuel

import Deriving.DepTyCheck.Gen

import public System.Random.Pure.StdGen

%default total

export
deriveFunExpr : RandomGen g => (seed : g) -> (maxAttempts : Nat) -> (fuel : Fuel) -> (signature : TTImp) -> Elab TTImp

public export
0 FunDerivationDefaults : Type -> Type
FunDerivationDefaults ty = {default someStdGen seed : _} ->
                           {default 10000 maxAttempts : Nat} ->
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

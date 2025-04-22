module DerivedGen

import Data.Nat

import Deriving.DepTyCheck.Gen

%default total

f : Nat -> (y : Nat) -> (0 _ : IsSucc y) => Nat
f x y = case (modNatNZ x y %search) of
  Z   => divNatNZ x y %search
  S _ => S (divNatNZ x y %search)

record NA where
  constructor MkNA
  curS : Nat
  {auto 0 curTotLTE : LTE curS curS}

data N : Nat -> NA -> Type where
  F : (0 nz : IsSucc c) =>
      {k : Nat} ->
      N c (MkNA (f k c) @{Relation.reflexive})

data NT : N cfg ar -> Type where
  NTF : NT $ F @{nz}

%language ElabReflection

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (cfg : Nat) -> (ar : NA) -> (node : N cfg ar) -> Gen MaybeEmpty $ NT node

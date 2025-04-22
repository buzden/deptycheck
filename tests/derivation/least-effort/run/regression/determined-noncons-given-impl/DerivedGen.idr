module DerivedGen

import RunDerivedGen

import Data.Fin

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
      N c $ MkNA (f k c) @{Relation.reflexive}

data NT : N cfg ar -> Type where
  NTF : NT $ F @{nz}

checkedGen : Fuel -> (cfg : Nat) -> (ar : NA) -> (node : N cfg ar) -> Gen MaybeEmpty $ NT node
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

Show (NT n) where
  show NTF = "NTF"

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 1 (MkNA 2) $ F {k=2}
  ]

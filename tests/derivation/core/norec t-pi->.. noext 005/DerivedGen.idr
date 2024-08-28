module DerivedGen

import Data.Fin

import Deriving.Show

import RunDerivedGen

%default total

%language ElabReflection

data FinEq : Fin n -> Fin n -> Type where
  Here  : FinEq FZ FZ
  These : {n : Nat} -> {0 i, j : Fin n} -> FinEq i j -> FinEq (FS i) (FS j)

data X : (n : Nat) -> Fin n -> Fin n -> Type where
  MkX : (i1, i2 : Fin n) -> (i1 `FinEq` i2) -> X n i1 i2

%hint ShowFinEq : {0 a, b : Fin n} -> Show (FinEq a b); ShowFinEq = %runElab derive

Show (X n i1 i2) where
  show $ MkX i1 i2 prf = "MkX \{show i1} \{show i2} \{show prf}"

checkedGen : Fuel -> (n : Nat) -> (i1 : Fin n) -> (i2 : Fin n) -> Gen MaybeEmpty (X n i1 i2)
checkedGen = deriveGen

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 3 0 1
  , G $ \fl => checkedGen fl 3 1 1
  , G $ \fl => checkedGen fl 3 2 1
  , G $ \fl => checkedGen fl 3 2 2
  ]

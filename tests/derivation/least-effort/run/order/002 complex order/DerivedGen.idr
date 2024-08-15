module DerivedGen

import RunDerivedGen

import Data.Fin

import Deriving.Show

%default total

%language ElabReflection

data BS : (n : Nat) -> Type where
  MkBS : BS n

h : Fin n -> BS n -> BS n
h i MkBS = MkBS

data X : (n : Nat) -> BS n -> Type where
  X0 : X 1 bs
  X2 : X 3 bs

data Y : (n : Nat) -> Fin n -> BS n -> Type where
  Y0 : Y 1 i bs
  Y2 : Y 3 2 bs

data Z : Type where
  MkZ : (n : Nat) -> (i : Fin n) -> (bs : BS n) -> (x : X n (h i bs)) -> (y : Y n i bs) -> Z

%hint ShowBS : Show (BS n); ShowBS = %runElab derive
%hint ShowX : Show (X n bs); ShowX = %runElab derive
%hint ShowY : Show (Y n i bs); ShowY = %runElab derive
%hint ShowZ : Show Z; ShowZ = %runElab derive

checkedGen : Fuel -> Gen MaybeEmpty Z
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]

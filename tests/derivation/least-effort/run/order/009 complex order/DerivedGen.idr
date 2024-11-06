module DerivedGen

import RunDerivedGen

import Data.Fin

import Deriving.Show

%default total

%language ElabReflection

data X : Nat -> Type where
  X0 : X x
  X2 : X x

data Y : (n : Nat) -> Fin n -> Type where
  Y0 : Y 1 i
  Y2 : Y 3 2

data Z : Type where
  MkZ : (n : Nat) -> (i : Fin n) -> (x : X (n + 2)) -> (y : Y n i) -> Z

%hint ShowX : Show (X n); ShowX = %runElab derive
%hint ShowY : Show (Y n i); ShowY = %runElab derive
%hint ShowZ : Show Z; ShowZ = %runElab derive

checkedGen : Fuel -> Gen MaybeEmpty Z
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]

module DerivedGen

import RunDerivedGen

import Data.Fin

import Deriving.Show

%default total

%language ElabReflection

g : {n : _} -> Fin n -> Fin n
g = finS

data Y : (n : Nat) -> Fin n -> Type where
  Y1 : Y 1 i
  Y2 : Y 2 1

data Z : Type where
  MkZ : (n : Nat) -> (x : Fin n) -> (y : Y n (g x)) -> Z

%hint ShowY : Show (Y n i); ShowY = %runElab derive
%hint ShowZ : Show Z; ShowZ = %runElab derive

checkedGen : Fuel -> Gen MaybeEmpty Z
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]

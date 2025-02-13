module DerivedGen

import Deriving.Show

import RunDerivedGen

%default total

%language ElabReflection

data X : Nat -> Type where
  MkX : (n : Nat) -> X n

%hint ShowX : Show (X n); ShowX = %runElab derive

data Y : Nat -> Type where
  MkY : X n -> X n -> Y n

%hint ShowY : Show (Y n); ShowY = %runElab derive

data Z : Y n -> Type where
  End : Z (MkY x x2)
  Go  : Z (MkY x x1) -> Z (MkY x x2)

Show (Z y) where
  show End = "|"
  show (Go c) = "." ++ show c

checkedGen : Fuel -> (n : Nat) -> Gen MaybeEmpty (y : Y n ** Z y)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 0
  , G $ \fl => checkedGen fl 1
  , G $ \fl => checkedGen fl 2
  , G $ \fl => checkedGen fl 10
  ]

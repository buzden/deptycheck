module DerivedGen

import Deriving.Show

import RunDerivedGen

%default total

%language ElabReflection

data X : Bool -> Type where
  MkX : (b : Bool) -> X b

%hint ShowX : Show (X n); ShowX = %runElab derive

data Y : Bool -> Type where
  MkY : X b -> X b -> Y b

%hint ShowY : Show (Y n); ShowY = %runElab derive

data Z : Y b -> Type where
  End : Z y
  Go  : Z (MkY x x1) -> Z (MkY x x2)

Show (Z y) where
  show End = "|"
  show (Go c) = "." ++ show c

checkedGen : Fuel -> (b : Bool) -> (y : Y b) -> Gen MaybeEmpty $ Z y
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl True  (MkY (MkX ?) (MkX ?))
  , G $ \fl => checkedGen fl False (MkY (MkX ?) (MkX ?))
  ]

module DerivedGen

import Deriving.Show

import RunDerivedGen

%default total

%language ElabReflection

data X : Bool -> Type where
  MkX0 : X b
  MkX1 : X b

data Y : X b -> X b -> Type where
  MkY0 : Y rndX MkX1 => Y MkX1 unusedX
  MkY1 : Y MkX1 unusedX

data Z : X b -> Type where
  MkZ : Y x MkX0 => Z x

checkedGen : Fuel -> (b : _) -> (x : X b) -> Gen MaybeEmpty (Z x)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

%hint ShowX : Show (X b); ShowX = %runElab derive
%hint ShowY : Show (Y x1 x2); ShowY = %runElab derive
Show (Z y) where
  show (MkZ @{y}) = "MkZ @{\{show y}}"

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl True  MkX0
  , G $ \fl => checkedGen fl True  MkX1
  , G $ \fl => checkedGen fl False MkX0
  , G $ \fl => checkedGen fl False MkX1
  ]

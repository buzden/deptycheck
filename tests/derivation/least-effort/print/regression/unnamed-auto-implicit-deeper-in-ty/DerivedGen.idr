module DerivedGen

import Deriving.DepTyCheck.Gen

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

%runElab deriveGenPrinter $ Fuel -> (b : _) -> (x : X b) -> Gen MaybeEmpty (Z x)

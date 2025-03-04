module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

import Data.Vect

%default total

%language ElabReflection

mutual

  data X = X0 | X1 | X2 Y

  data Y = Y0 | Y1 X

%runElab deriveGenPrinter @{EmptyCons} $ Fuel -> Gen MaybeEmpty X

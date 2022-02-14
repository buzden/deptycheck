module DerivedGen

import AlternativeCore
import PrintDerivation

import Data.Vect

%default total

%language ElabReflection

data Y = Y0 | Y1

data X = X0 | X1 | X2 Y

%runElab printDerived @{EmptyCons} $ Fuel -> Gen X

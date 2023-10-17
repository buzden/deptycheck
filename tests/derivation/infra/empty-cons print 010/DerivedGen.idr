module DerivedGen

import AlternativeCore
import PrintDerivation

import Data.Vect

%default total

%language ElabReflection

mutual

  data X = X0 | X1 | X2 Y

  data Y = Y0 | Y1 X

%runElab printDerived {core=EmptyCons} $ Fuel -> Gen MaybeEmpty X

module DerivedGen

import AlternativeCore
import PrintDerivation

import Data.Vect

%default total

%language ElabReflection

mutual

  data X : Type -> Type where
    X0 : X a
    X1 : X Nat
    X2 : X Y

  data Y = Y0 | Y1 (X Nat)

%runElab printDerived {core=EmptyCons} $ Fuel -> Gen MaybeEmpty (a ** X a)

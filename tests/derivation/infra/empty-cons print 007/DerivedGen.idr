module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data X : Nat -> Bool -> Type where
  X0 : X 0 True
  X1 : X 1 False

%runElab printDerived {core=EmptyCons} $ Fuel -> Gen MaybeEmpty (n : Nat ** b : Bool ** X n b)

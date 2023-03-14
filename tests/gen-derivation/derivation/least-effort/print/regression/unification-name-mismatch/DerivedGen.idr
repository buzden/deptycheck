module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

%hint
UsedConstructorDerivator : ConstructorDerivator
UsedConstructorDerivator = LeastEffort

data X : Type where
  Nil : X
  (::) : Unit -> X -> X

data Y : (xs : X) -> (ys : X) -> Type where
  A : Y (x :: xs) (x :: xs)
  B : Y xs ys -> Y (x :: xs) (y :: ys)

%runElab printDerived $ Fuel -> (xs : X) -> (ys : X) -> Gen0 $ Y xs ys

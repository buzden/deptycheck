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

DecEq X where
  [] `decEq` [] = Yes Refl
  [] `decEq` (y :: ys) = No $ \case Refl impossible
  (x :: xs) `decEq` [] = No $ \case Refl impossible
  (() :: xs) `decEq` (() :: ys) = case xs `decEq` ys of
                                    (Yes prf) => rewrite prf in Yes Refl
                                    (No contra) => No $ \prf => ?wut

data Y : (xs : X) -> (ys : X) -> Type where
  A : Y (x :: xs) (x :: xs)
  B : Y xs ys -> Y (x :: xs) (y :: ys)

%runElab printDerived $ Fuel -> (xs : X) -> (ys : X) -> Gen $ Y xs ys

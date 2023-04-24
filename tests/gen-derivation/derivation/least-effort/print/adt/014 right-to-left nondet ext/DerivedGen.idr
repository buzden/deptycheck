module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data X : String -> Nat -> Type where
  MkX : (n : _) -> (m : _) -> X n m

data Y : Type where
  MkY : X n m -> X n k -> Y

%runElab printDerived @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen CanBeEmptyStatic String) => (Fuel -> Gen CanBeEmptyStatic Nat) => Gen CanBeEmptyStatic Y

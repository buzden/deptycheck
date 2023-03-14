module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data X : String -> Nat -> Type where
  MkX : (n : _) -> (m : _) -> X n m

data Y : Type where
  MkY : X n m -> X n k -> Y

%runElab printDerived @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen0 String) => (Fuel -> Gen0 Nat) => Gen0 Y

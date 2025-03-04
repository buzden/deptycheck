module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : String -> Nat -> Type where
  MkX : (n : _) -> (m : _) -> X n m

data Y : Type where
  MkY : X n m -> X n k -> Y

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty Y

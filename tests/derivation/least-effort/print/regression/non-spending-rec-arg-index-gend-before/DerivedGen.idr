module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data Tag = A | B

data W = MkW Tag

data X : Nat -> W -> Type where
  L : X n w
  N : X (S n) (MkW t) -> X n w -> X (S n) w

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (n : Nat) -> (w : W) -> Gen MaybeEmpty (X n w)

module Test

import Shared

%default total

%language ElabReflection

data X : (n : Nat) -> Fin n -> Type where
  MkX : X 5 4

%runElab specialiseDataLam' "Y" $ \a, b => X a b

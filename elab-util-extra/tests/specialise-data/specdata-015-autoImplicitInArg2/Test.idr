module Test

import Shared

%language ElabReflection

data Z : Type -> Type where
  MkZ : Semigroup x => (a, b : x) -> (f : x -> Type) -> f (a <+> b) -> Z x

%runElab specialiseDataLam' "Z'" $ Z (List Nat)

z0 : Z'
z0 = MkZ [0] [1, 2] (Any $ \x => x = 0) (Here Refl)

z1 : Z'
z1 = MkZ [0] [1, 2] (Any $ \x => x = 1) (There $ Here Refl)

module Test

import Shared

%language ElabReflection

data X : Type -> (Type -> Type) -> Type where
  MkX : f a -> f Nat -> f String -> f (f a) -> X a f

%runElab specialiseData' "X'" $ X (Fin 5) List

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
x0' = %runElab verifySpecialisation (X (Fin 5) List) X'
  [ `(MkX [FZ, FS FZ] [5,6,7,8] ["9", "10"] [[0],[1],[2]])
  ]

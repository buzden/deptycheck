module Test

import Shared

%language ElabReflection

-- The specialiser in its current form does *not* support type aliases!
failing "Internal error: failed to get type info"
  %runElab specialiseData' "Eq3" $ \x => x = 3

%runElab specialiseData' "Eq3'" $ \x : Nat => Builtin.Equal x 3

failing "Mismatch between: ?x = ?x and Eq3' 3."
  e0 : Eq3' 3
  e0 = Refl

%runElab specialiseData' "Eq3" $ \x : Nat => Builtin.Equal x (the Nat 3)

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e1' = %runElab verifySpecialisation
  (Builtin.Equal (the Nat 3) (the Nat 3))
  (Eq3 (the Nat 3))
  [`(Refl)]

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e1'' = %runElab verifyEmptyType (0=3) (Eq3 0)

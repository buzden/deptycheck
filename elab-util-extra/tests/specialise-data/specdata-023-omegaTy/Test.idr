module Test

import Shared

%language ElabReflection

data X : Type -> Type -> Type where
  MkX : (t, f : Type) -> X t f

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
%runElab specialiseData' "X'" $ \x => X x Nat

x1' = %runElab verifySpecialisation' (X Nat Nat) (X' Nat)
  [(`(MkX Nat Nat),`(MkX Nat))]

x2' = %runElab verifySpecialisation' (X String Nat) (X' String)
  [(`(MkX String Nat),`(MkX String))]
-- failing "Mismatch between: ?x = ?x and Eq3' 3."
--   e0 : Eq3' 3
--   e0 = Refl

-- %runElab specialiseData' "Eq3" $ \x : Nat => Builtin.Equal x (the Nat 3)

-- --- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
-- e1' = %runElab verifySpecialisation
--   (Builtin.Equal (the Nat 3) (the Nat 3))
--   (Eq3 (the Nat 3))
--   [`(Refl)]

-- --- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
-- e1'' = %runElab verifyEmptyType (0=3) (Eq3 0)

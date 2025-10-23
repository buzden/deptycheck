module Test

import Shared

%language ElabReflection

-- The specialiser in its current form does *not* support type aliases!
failing "Builtin.(===) is not a type"
  %runElab specialiseData' "EqNat" $ \x => x = Nat

-- Having a non-M0 type parameter in the lambda leads to our cast implementation not being covering. TODO: Investigate further?
failing "pToMImpl is not covering."
  %runElab specialiseData' "EqNat2" $ \x : Type => Builtin.Equal x Nat

%runElab specialiseData' "EqNat" $ \0 x : Type => Builtin.Equal x Nat

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e1' = %runElab verifySpecialisation (Nat = Nat) (EqNat Nat) [`(Refl)]

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e1'' = %runElab verifyEmptyType (String === Nat) (EqNat String)

%runElab specialiseData' "EqNat2" $ Builtin.Equal Nat Nat

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e2' = %runElab verifySpecialisation (Nat = Nat) (EqNat2) [`(Refl)]

%runElab specialiseData' "EqNat3" $ Builtin.Equal String Nat

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e2'' = %runElab verifyEmptyType (String === Nat) (EqNat3)

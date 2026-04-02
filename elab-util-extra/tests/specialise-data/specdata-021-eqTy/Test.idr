module Test

import Shared

%language ElabReflection

-- The specialiser in its current form does *not* support type aliases!
failing "MissingTypeInfoError Builtin.(===)"
  %runElab specialiseDataLam' "EqNat" $ \x => x = Nat

%runElab specialiseDataLam' "EqNatMW" $ \x : Type => Builtin.Equal x Nat

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e0' = %runElab verifySpecialisation (Nat = Nat) (EqNatMW Nat) [`(Refl)]

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e0'' = %runElab verifyEmptyType (String === Nat) (EqNatMW String)

%runElab specialiseDataLam' "EqNatM0" $ \0 x : Type => Builtin.Equal x Nat

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e1' = %runElab verifySpecialisation (Nat = Nat) (EqNatM0 Nat) [`(Refl)]

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e1'' = %runElab verifyEmptyType (String === Nat) (EqNatM0 String)

%runElab specialiseDataLam' "EqNat2" $ Builtin.Equal Nat Nat

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e2' = %runElab verifySpecialisation (Nat = Nat) (EqNat2) [`(Refl)]

%runElab specialiseDataLam' "EqNat3" $ Builtin.Equal String Nat

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e2'' = %runElab verifyEmptyType (String === Nat) (EqNat3)

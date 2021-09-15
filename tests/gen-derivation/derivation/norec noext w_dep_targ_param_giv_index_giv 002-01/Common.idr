module Common

import public Test.DepTyCheck.Gen.Auto

%default total

export
Show (a = b) where
  show Refl = "Refl"

export
derivedGen : Fuel -> (a, b : Nat) -> Gen (a = b)
--derivedGen = deriveGen
derivedGen _ _ _ = empty

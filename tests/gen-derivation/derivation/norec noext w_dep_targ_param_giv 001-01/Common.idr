module Common

import public Test.DepTyCheck.Gen.Auto

%default total

export
-- both type arguments are parameters, not indices
data X : Bool -> Bool -> Type where
  MkX : (b1 : Bool) -> (b2 : Bool) -> X b1 b2

export
Show (X b1 b2) where
  show (MkX b1 b2) = "MkX \{show b1} \{show b2}"

export
derivedGen : Fuel -> (b1 : Bool) -> (b2 : Bool) -> Gen (X b1 b2)
--derivedGen = deriveGen
derivedGen _ _ _ = empty

module ValidateInput

import Test.DepTyCheck.Gen.Auto

%language ElabReflection

%default total

data Y : Type -> Type -> Type where
  MkY : Y Int String

--- Non-Gen type ---

list : List Int
list = deriveGen

list' : Fuel -> List Int
list' = deriveGen

y : Y Int String
y = deriveGen

y' : Fuel -> Y Int String
y' = deriveGen

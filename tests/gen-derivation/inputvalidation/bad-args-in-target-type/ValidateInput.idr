module ValidateInput

import Test.DepTyCheck.Gen.Auto

%language ElabReflection

%default total

data Y : Type -> Type -> Type where
  MkY : Y Int String

--- Non-variable arguments of the target type ---

genY_Int : Fuel -> (a : Type) -> Gen $ Y a Int
genY_Int = deriveGen

genY_same_param : Fuel -> (a : Type) -> Gen $ Y a a
genY_same_param = deriveGen

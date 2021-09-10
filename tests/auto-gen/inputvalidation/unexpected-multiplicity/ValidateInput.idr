module ValidateInput

import Test.DepTyCheck.Gen.Auto

%language ElabReflection

%default total

data X = MkX

data X' = MkX'

data Y : Type -> Type -> Type where
  MkY : Y Int String

--- Unexpected zero and linear arguments ---

genY_given_zero_fuel : (0 _ : Fuel) -> (a, b : Type) -> Gen $ Y a b
genY_given_zero_fuel = deriveGen

genY_given_zero_arg1 : Fuel -> (0 a : Type) -> (b : Type) -> Gen $ Y a b
genY_given_zero_arg1 = deriveGen

genY_given_zero_args : Fuel -> (0 a, b : Type) -> Gen $ Y a b
genY_given_zero_args = deriveGen

genY_given_lin_fuel : (1 _ : Fuel) -> (a, b : Type) -> Gen $ Y a b
genY_given_lin_fuel = deriveGen

genY_given_lin_arg1 : Fuel -> (1 a : Type) -> (b : Type) -> Gen $ Y a b
genY_given_lin_arg1 = deriveGen

genY_given_lin_args : Fuel -> (1 a, b : Type) -> Gen $ Y a b
genY_given_lin_args = deriveGen

genY_given_zero_lin_args : Fuel -> (0 a : Type) -> (1 b : Type) -> Gen $ Y a b
genY_given_zero_lin_args = deriveGen

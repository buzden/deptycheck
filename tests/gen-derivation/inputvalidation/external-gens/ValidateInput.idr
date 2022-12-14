module ValidateInput

import Deriving.DepTyCheck.Gen

%language ElabReflection

%default total

data X = MkX

data X' = MkX'

data Y : Type -> Type -> Type where
  MkY : Y Int String

--- Repeating external gens ---

genY_repX_autoimpl : Fuel -> (Fuel -> Gen X) => (Fuel -> Gen X) => (a, b : Type) -> Gen $ Y a b
genY_repX_autoimpl = deriveGen

--- Non-gen externals ---

genY_nongen_autoimpl_list : Fuel -> (Fuel -> List Int) => (a, b : Type) -> Gen $ Y a b
genY_nongen_autoimpl_list = deriveGen

genY_nongen_autoimpl_pair : Fuel -> (Fuel -> Gen X, Fuel -> Gen X') => (a, b : Type) -> Gen $ Y a b
genY_nongen_autoimpl_pair = deriveGen

genY_nongen_autoimpl_dpair : Fuel -> (Fuel -> (a ** b ** Gen $ Y a b)) => (a, b : Type) -> Gen $ Y a b
genY_nongen_autoimpl_dpair = deriveGen

--- Externals with no fuel ---

genY_nongen_autoimpl_list_nofuel : Fuel -> List Int => (a, b : Type) -> Gen $ Y a b
genY_nongen_autoimpl_list_nofuel = deriveGen

genY_nongen_autoimpl_pair_nofuel : Fuel -> (Gen X, Gen X') => (a, b : Type) -> Gen $ Y a b
genY_nongen_autoimpl_pair_nofuel = deriveGen

genY_nongen_autoimpl_dpair_nofuel : Fuel -> (a ** b ** Gen $ Y a b) => (a, b : Type) -> Gen $ Y a b
genY_nongen_autoimpl_dpair_nofuel = deriveGen

--- Result is alteady in externals ---

genY_require_self_autoimpl : Fuel -> (Fuel -> Gen X) => (Fuel -> (a, b : Type) -> Gen $ Y a b) => (a, b : Type) -> Gen $ Y a b
genY_require_self_autoimpl = deriveGen

--- Auto-implicits are present inside auto-implicits ---

genY_autoimpl_in_autoimpl : Fuel -> (Fuel -> (Fuel -> (a, b : Type) -> Gen $ Y a b) => (a : Type) -> Gen (b ** Y a b)) => Gen (a ** b ** Y a b)
genY_autoimpl_in_autoimpl = deriveGen

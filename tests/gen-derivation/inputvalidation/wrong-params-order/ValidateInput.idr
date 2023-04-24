module ValidateInput

import Deriving.DepTyCheck.Gen

%language ElabReflection

%default total

data X = MkX

data Y : Type -> Type -> Type where
  MkY : Y Int String

--- Auto-implicits not right after the `Fuel` parameter ---

-- TODO to add if it is needed

--- Wrong order of parameters ---

genY_wrong_giv_order : Fuel -> (b, a : Type) -> Gen CanBeEmptyStatic $ Y a b
genY_wrong_giv_order = deriveGen

genX_wrong_giv_order_autoimpl : Fuel -> (Fuel -> (b, a : Type) -> Gen CanBeEmptyStatic $ Y a b) => Gen CanBeEmptyStatic X
genX_wrong_giv_order_autoimpl = deriveGen

genX_wrong_giv_order_autoimpl_rep : Fuel -> (Fuel -> (b, a : Type) -> Gen CanBeEmptyStatic $ Y a b) => (Fuel -> (a, b : Type) -> Gen CanBeEmptyStatic $ Y a b) => Gen CanBeEmptyStatic X
genX_wrong_giv_order_autoimpl_rep = deriveGen

genY_wrong_gened_order : Fuel -> Gen CanBeEmptyStatic (b : Type ** a : Type ** Y a b)
genY_wrong_gened_order = deriveGen

genY_wrong_gened_order' : Fuel -> Gen CanBeEmptyStatic (b ** a ** Y a b)
genY_wrong_gened_order' = deriveGen

genX_wrong_gened_order_autoimpl : Fuel -> (Fuel -> Gen CanBeEmptyStatic (b : Type ** a : Type ** Y a b)) => Gen CanBeEmptyStatic X
genX_wrong_gened_order_autoimpl = deriveGen

genX_wrong_gened_order_autoimpl_rep : Fuel -> (Fuel -> Gen CanBeEmptyStatic (b : Type ** a : Type ** Y a b)) => (Fuel -> Gen CanBeEmptyStatic (a : Type ** b : Type ** Y a b)) => Gen CanBeEmptyStatic X
genX_wrong_gened_order_autoimpl_rep = deriveGen

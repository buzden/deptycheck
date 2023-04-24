module ValidateInput

import Deriving.DepTyCheck.Gen

%language ElabReflection

%default total

data X = MkX

data Y : Type -> Type -> Type where
  MkY : Y Int String

--- Gen CanBeEmptyStatic of strange things ---

genOfConcreteGen : Fuel -> Gen CanBeEmptyStatic $ Gen CanBeEmptyStatic X
genOfConcreteGen = deriveGen

genOfLazies : Fuel -> Gen CanBeEmptyStatic $ Lazy X
genOfLazies = deriveGen

genOfInfs : Fuel -> Gen CanBeEmptyStatic $ Inf X
genOfInfs = deriveGen

genOfDPair : Fuel -> (a ** b ** Gen CanBeEmptyStatic $ Y a b)
genOfDPair = deriveGen

genOfPair : Fuel -> (a, b : Type) -> (Gen (Y a b), Gen CanBeEmptyStatic (Y a b))
genOfPair = deriveGen

genOfPair' : Fuel -> (a, b : Type) -> (Gen (Y a b), Gen CanBeEmptyStatic X)
genOfPair' = deriveGen

genOfFuns_pur : Fuel -> Gen CanBeEmptyStatic $ (a : Type) -> (b : Type) -> Y a b
genOfFuns_pur = deriveGen

genOfFuns_pur0s : Fuel -> Gen CanBeEmptyStatic $ (0 a : Type) -> (0 b : Type) -> Y a b
genOfFuns_pur0s = deriveGen

genOfFuns_pur1s : Fuel -> Gen CanBeEmptyStatic $ (1 a : Type) -> (1 b : Type) -> Y a b
genOfFuns_pur1s = deriveGen

genOfFuns_ins_pair : Fuel -> Gen CanBeEmptyStatic (a ** ((b : Type) -> Y a b))
genOfFuns_ins_pair = deriveGen

genOfFuns_ins_pair0 : Fuel -> Gen CanBeEmptyStatic (a ** ((0 b : Type) -> Y a b))
genOfFuns_ins_pair0 = deriveGen

genOfFuns_ins_pair1 : Fuel -> Gen CanBeEmptyStatic (a ** ((1 b : Type) -> Y a b))
genOfFuns_ins_pair1 = deriveGen

genOfFuns_out_pair : Fuel -> Gen CanBeEmptyStatic $ (b : Type) -> (a ** Y a b)
genOfFuns_out_pair = deriveGen

genOfFuns_out_pair0 : Fuel -> Gen CanBeEmptyStatic $ (0 b : Type) -> (a ** Y a b)
genOfFuns_out_pair0 = deriveGen

genOfFuns_out_pair1 : Fuel -> Gen CanBeEmptyStatic $ (1 b : Type) -> (a ** Y a b)
genOfFuns_out_pair1 = deriveGen

-- TODO to add more type that cannot be said as "pure types inside a `Gen`", if needed.

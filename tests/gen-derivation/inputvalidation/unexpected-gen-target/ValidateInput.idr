module ValidateInput

import Deriving.DepTyCheck.Gen

%language ElabReflection

%default total

data X = MkX

data Y : Type -> Type -> Type where
  MkY : Y Int String

--- Gen0 of strange things ---

genOfConcreteGen : Fuel -> Gen0 $ Gen0 X
genOfConcreteGen = deriveGen

genOfLazies : Fuel -> Gen0 $ Lazy X
genOfLazies = deriveGen

genOfInfs : Fuel -> Gen0 $ Inf X
genOfInfs = deriveGen

genOfDPair : Fuel -> (a ** b ** Gen0 $ Y a b)
genOfDPair = deriveGen

genOfPair : Fuel -> (a, b : Type) -> (Gen (Y a b), Gen0 (Y a b))
genOfPair = deriveGen

genOfPair' : Fuel -> (a, b : Type) -> (Gen (Y a b), Gen0 X)
genOfPair' = deriveGen

genOfFuns_pur : Fuel -> Gen0 $ (a : Type) -> (b : Type) -> Y a b
genOfFuns_pur = deriveGen

genOfFuns_pur0s : Fuel -> Gen0 $ (0 a : Type) -> (0 b : Type) -> Y a b
genOfFuns_pur0s = deriveGen

genOfFuns_pur1s : Fuel -> Gen0 $ (1 a : Type) -> (1 b : Type) -> Y a b
genOfFuns_pur1s = deriveGen

genOfFuns_ins_pair : Fuel -> Gen0 (a ** ((b : Type) -> Y a b))
genOfFuns_ins_pair = deriveGen

genOfFuns_ins_pair0 : Fuel -> Gen0 (a ** ((0 b : Type) -> Y a b))
genOfFuns_ins_pair0 = deriveGen

genOfFuns_ins_pair1 : Fuel -> Gen0 (a ** ((1 b : Type) -> Y a b))
genOfFuns_ins_pair1 = deriveGen

genOfFuns_out_pair : Fuel -> Gen0 $ (b : Type) -> (a ** Y a b)
genOfFuns_out_pair = deriveGen

genOfFuns_out_pair0 : Fuel -> Gen0 $ (0 b : Type) -> (a ** Y a b)
genOfFuns_out_pair0 = deriveGen

genOfFuns_out_pair1 : Fuel -> Gen0 $ (1 b : Type) -> (a ** Y a b)
genOfFuns_out_pair1 = deriveGen

-- TODO to add more type that cannot be said as "pure types inside a `Gen`", if needed.

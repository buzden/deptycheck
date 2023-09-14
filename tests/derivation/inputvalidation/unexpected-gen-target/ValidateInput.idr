module ValidateInput

import Deriving.DepTyCheck.Gen

%language ElabReflection

%default total

data X = MkX

data Y : Type -> Type -> Type where
  MkY : Y Int String

--- Gen MaybeEmpty of strange things ---

genOfConcreteGen : Fuel -> Gen MaybeEmpty $ Gen MaybeEmpty X
genOfConcreteGen = deriveGen

genOfLazies : Fuel -> Gen MaybeEmpty $ Lazy X
genOfLazies = deriveGen

genOfInfs : Fuel -> Gen MaybeEmpty $ Inf X
genOfInfs = deriveGen

genOfDPair : Fuel -> (a ** b ** Gen MaybeEmpty $ Y a b)
genOfDPair = deriveGen

genOfPair : Fuel -> (a, b : Type) -> (Gen MaybeEmpty (Y a b), Gen MaybeEmpty (Y a b))
genOfPair = deriveGen

genOfPair' : Fuel -> (a, b : Type) -> (Gen MaybeEmpty (Y a b), Gen MaybeEmpty X)
genOfPair' = deriveGen

genOfFuns_pur : Fuel -> Gen MaybeEmpty $ (a : Type) -> (b : Type) -> Y a b
genOfFuns_pur = deriveGen

genOfFuns_pur0s : Fuel -> Gen MaybeEmpty $ (0 a : Type) -> (0 b : Type) -> Y a b
genOfFuns_pur0s = deriveGen

genOfFuns_pur1s : Fuel -> Gen MaybeEmpty $ (1 a : Type) -> (1 b : Type) -> Y a b
genOfFuns_pur1s = deriveGen

genOfFuns_ins_pair : Fuel -> Gen MaybeEmpty (a ** ((b : Type) -> Y a b))
genOfFuns_ins_pair = deriveGen

genOfFuns_ins_pair0 : Fuel -> Gen MaybeEmpty (a ** ((0 b : Type) -> Y a b))
genOfFuns_ins_pair0 = deriveGen

genOfFuns_ins_pair1 : Fuel -> Gen MaybeEmpty (a ** ((1 b : Type) -> Y a b))
genOfFuns_ins_pair1 = deriveGen

genOfFuns_out_pair : Fuel -> Gen MaybeEmpty $ (b : Type) -> (a ** Y a b)
genOfFuns_out_pair = deriveGen

genOfFuns_out_pair0 : Fuel -> Gen MaybeEmpty $ (0 b : Type) -> (a ** Y a b)
genOfFuns_out_pair0 = deriveGen

genOfFuns_out_pair1 : Fuel -> Gen MaybeEmpty $ (1 b : Type) -> (a ** Y a b)
genOfFuns_out_pair1 = deriveGen

nonEmptyGen : Fuel -> Gen NonEmpty X
nonEmptyGen = deriveGen

-- TODO to add more type that cannot be said as "pure types inside a `Gen`", if needed.

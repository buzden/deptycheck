module ValidateInput

import Test.DepTyCheck.Gen.Auto

%language ElabReflection

%default total

-----------------------
--- Data structures ---
-----------------------

data X = MkX

data X' = MkX'

data Y : Type -> Type -> Type where
  MkY : Y Int String

------------------------------------
--- Compiling, but bad signature ---
------------------------------------

--- Non-Gen type ---

list : List Int
list = deriveGen

y : Y Int String
y = deriveGen

--- No fuel argument ---

genY_noFuel_given : (a, b : Type) -> Gen $ Y a b
genY_noFuel_given = deriveGen

genY_noFuel_mid : (b : Type) -> Gen (a ** Y a b)
genY_noFuel_mid = deriveGen

genY_noFuel_mid' : (b : Type) -> Gen $ DPair {a = Type, p = \a => Y a b}
genY_noFuel_mid' = deriveGen

genY_noFuel_gened : Gen (a ** b ** Y a b)
genY_noFuel_gened = deriveGen

--- Misplaced fuel argument ---

genY_missplFuel_aft : (a, b : Type) -> Fuel -> Gen $ Y a b
genY_missplFuel_aft = deriveGen

genY_missplFuel_mid : (a : Type) -> Fuel -> (b : Type) -> Gen $ Y a b
genY_missplFuel_mid = deriveGen

genY_missplFuel_aft_autoimpl : Gen X => Fuel -> (a, b : Type) -> Gen $ Y a b
genY_missplFuel_aft_autoimpl = deriveGen

--- Unrelated stuff in the resulting dpair ---

genY_with_unrelated : Fuel -> (a : Type) -> (b : Type ** n : Nat ** Y a b)
genY_with_unrelated = deriveGen

--- Gen of strange things ---

genOfGens : Fuel -> Gen $ Gen X
genOfGens = deriveGen

genOfLazies : Fuel -> Gen $ Lazy X
genOfLazies = deriveGen

genOfInfs : Fuel -> Gen $ Inf X
genOfInfs = deriveGen

genOfDPair : Fuel -> (a ** b ** Gen $ Y a b)
genOfDPair = deriveGen

genOfFuns_pur : Fuel -> Gen $ (a : Type) -> (b : Type) -> Y a b
genOfFuns_pur = deriveGen

genOfFuns_pur0s : Fuel -> Gen $ (0 a : Type) -> (0 b : Type) -> Y a b
genOfFuns_pur0s = deriveGen

genOfFuns_pur1s : Fuel -> Gen $ (1 a : Type) -> (1 b : Type) -> Y a b
genOfFuns_pur1s = deriveGen

genOfFuns_ins_pair : Fuel -> Gen $ (a ** (b : Type) -> Y a b)
genOfFuns_ins_pair = deriveGen

genOfFuns_ins_pair0 : Fuel -> Gen $ (a ** (0 b : Type) -> Y a b)
genOfFuns_ins_pair0 = deriveGen

genOfFuns_ins_pair1 : Fuel -> Gen $ (a ** (1 b : Type) -> Y a b)
genOfFuns_ins_pair1 = deriveGen

genOfFuns_out_pair : Fuel -> Gen $ (b : Type) -> (a ** Y a b)
genOfFuns_out_pair = deriveGen

genOfFuns_out_pair0 : Fuel -> Gen $ (0 b : Type) -> (a ** Y a b)
genOfFuns_out_pair0 = deriveGen

genOfFuns_out_pair1 : Fuel -> Gen $ (1 b : Type) -> (a ** Y a b)
genOfFuns_out_pair1 = deriveGen

-- TODO to add more type that cannot be said as "pure types inside a `Gen`", if needed.

--- Non-variable arguments of the target type ---

genY_Int : Fuel -> (a : Type) -> Gen $ Y a Int
genY_Int = deriveGen

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

--- Gen for type with no constructors ---

genVoid : Fuel -> Gen Void
genVoid = deriveGen

--- Repeating external gens ---

genY_repX_hinted : Fuel -> (a, b : Type) -> Gen $ Y a b
genY_repX_hinted = deriveGen {externalHintedGens = [ `(Gen X), `(Gen X) ]}

genY_repX_autoimpl : Fuel -> Gen X => Gen X => (a, b : Type) -> Gen $ Y a b
genY_repX_autoimpl = deriveGen

genY_repX_both : Fuel -> Gen X => (a, b : Type) -> Gen $ Y a b
genY_repX_both = deriveGen {externalHintedGens = [ `(Gen X) ]}

genY_repX_both' : Fuel -> Gen X => Gen X => (a, b : Type) -> Gen $ Y a b
genY_repX_both' = deriveGen {externalHintedGens = [ `(Gen X), `(Gen X) ]}

--- Non-existent hinted gens ---

genY_nonex_hinted : Fuel -> (a, b : Type) -> Gen $ Y a b
genY_nonex_hinted = deriveGen {externalHintedGens = [ `(Gen NonExistent) ]}

genY_nonex_hinted' : Fuel -> (a, b : Type) -> Gen $ Y a b
genY_nonex_hinted' = deriveGen {externalHintedGens = [ `(forall a. Gen $ NonExistent a) ]}

genY_nonex_hinted'' : Fuel -> (a, b : Type) -> Gen $ Y a b
genY_nonex_hinted'' = deriveGen {externalHintedGens = [ `(Gen $ NonExistent a) ]}

--- Non-gen externals ---

genY_nongen_hinted_list : Fuel -> (a, b : Type) -> Gen $ Y a b
genY_nongen_hinted_list = deriveGen {externalHintedGens = [ `(List Int) ]}

genY_nongen_hinted_pair : Fuel -> (a, b : Type) -> Gen $ Y a b
genY_nongen_hinted_pair = deriveGen {externalHintedGens = [ `( (Gen X, Gen X') ) ]}

genY_nongen_hinted_dpair : Fuel -> (a, b : Type) -> Gen $ Y a b
genY_nongen_hinted_dpair = deriveGen {externalHintedGens = [ `( (a ** b ** Gen $ Y a b) ) ]}

genY_nongen_autoimpl_list : Fuel -> List Int => (a, b : Type) -> Gen $ Y a b
genY_nongen_autoimpl_list = deriveGen

genY_nongen_autoimpl_pair : Fuel -> (Gen X, Gen X') => (a, b : Type) -> Gen $ Y a b
genY_nongen_autoimpl_pair = deriveGen

genY_nongen_autoimpl_dpair : Fuel -> (a ** b ** Gen $ Y a b) => (a, b : Type) -> Gen $ Y a b
genY_nongen_autoimpl_dpair = deriveGen

--- Auto-implicits not right after the `Fuel` parameter ---

-- TODO to add if it is needed

--- Not all arguments are used ---

-- TODO to add if it is needed

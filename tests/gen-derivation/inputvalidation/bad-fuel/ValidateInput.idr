module ValidateInput

import Test.DepTyCheck.Gen.Auto

%language ElabReflection

%default total

data X = MkX

data Y : Type -> Type -> Type where
  MkY : Y Int String

--- No fuel argument ---

genY_noFuel_given : (a, b : Type) -> Gen $ Y a b
genY_noFuel_given = deriveGen

genY_noFuel_given' : Int -> (a, b : Type) -> Gen $ Y a b
genY_noFuel_given' = deriveGen

genY_noFuel_given'' : X -> (a, b : Type) -> Gen $ Y a b
genY_noFuel_given'' = deriveGen

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

--geY_missplFuel_aft_autoimpl : Gen X => Fuel -> (a, b : Type) -> Gen $ Y a b
--genY_missplFuel_aft_autoimpl = deriveGen
-- This test is commented out because the first auto-implicit argument `Gen X` does not
-- go into a type of `deriveGen`. Moreover, for now, it is impossible to manage with it,
-- because even explicit setting type argument of `deriveGen` makes two signatures incompatible.

--- Misplaced + implicit fuel argument ---

genY_missplFuel_aft_imp : (a, b : Type) -> {_ : Fuel} -> Gen $ Y a b
genY_missplFuel_aft_imp = deriveGen

genY_missplFuel_mid_imp : (a : Type) -> {_ : Fuel} -> (b : Type) -> Gen $ Y a b
genY_missplFuel_mid_imp = deriveGen

genY_missplFuel_aft_autoimpl_imp : Gen X => {_ : Fuel} -> (a, b : Type) -> Gen $ Y a b
genY_missplFuel_aft_autoimpl_imp = deriveGen

--- Implicit fuel argument ---

genY_unnamed_imp_fuel : {_ : Fuel} -> (a, b : Type) -> Gen $ Y a b
genY_unnamed_imp_fuel = deriveGen

genY_named_imp_fuel : {f : Fuel} -> (a, b : Type) -> Gen $ Y a b
genY_named_imp_fuel = deriveGen

genY_autoimp_fuel : Fuel => (a, b : Type) -> Gen $ Y a b
genY_autoimp_fuel = deriveGen

genY_defaulted_fuel : {default Dry fuel : Fuel} -> (a, b : Type) -> Gen $ Y a b
genY_defaulted_fuel = deriveGen

genY_defaulted_fuel' : {default (limit 120) fuel : Fuel} -> (a, b : Type) -> Gen $ Y a b
genY_defaulted_fuel' = deriveGen

--- Named explicit fuel ---

genY_exp_named_fuel : (fuel : Fuel) -> (a, b : Type) -> Gen $ Y a b
genY_exp_named_fuel = deriveGen

module ValidateInput

import Data.Fin

import Deriving.DepTyCheck.Gen

%language ElabReflection

%default total

data X = MkX

data Y : Type -> Type -> Type where
  MkY : Y Int String

--- Auto-implicits not right after the `Fuel` parameter ---

-- TODO to add if it is needed

--- Wrong order of parameters ---

genY_wrong_giv_order : Fuel -> (b, a : Type) -> Gen MaybeEmpty $ Y a b
genY_wrong_giv_order = deriveGen

genX_wrong_giv_order_autoimpl : Fuel -> (Fuel -> (b, a : Type) -> Gen MaybeEmpty $ Y a b) => Gen MaybeEmpty X
genX_wrong_giv_order_autoimpl = deriveGen

genX_wrong_giv_order_autoimpl_rep :
  Fuel -> (Fuel -> (b, a : Type) -> Gen MaybeEmpty $ Y a b) => (Fuel -> (a, b : Type) -> Gen MaybeEmpty $ Y a b) => Gen MaybeEmpty X
genX_wrong_giv_order_autoimpl_rep = deriveGen

genY_wrong_gened_order : Fuel -> Gen MaybeEmpty (b : Type ** a : Type ** Y a b)
genY_wrong_gened_order = deriveGen

genY_wrong_gened_order' : Fuel -> Gen MaybeEmpty (b ** a ** Y a b)
genY_wrong_gened_order' = deriveGen

genX_wrong_gened_order_autoimpl : Fuel -> (Fuel -> Gen MaybeEmpty (b : Type ** a : Type ** Y a b)) => Gen MaybeEmpty X
genX_wrong_gened_order_autoimpl = deriveGen

genX_wrong_gened_order_autoimpl_rep :
  Fuel -> (Fuel -> Gen MaybeEmpty (b : Type ** a : Type ** Y a b)) => (Fuel -> Gen MaybeEmpty (a : Type ** b : Type ** Y a b)) => Gen MaybeEmpty X
genX_wrong_gened_order_autoimpl_rep = deriveGen

---

data Z : Fin n -> Fin m -> Type where
  MkZ : Z {n=1} {m=S m} 0 0

genZ_nfmg : Fuel -> {n : Nat} -> (f : Fin n) -> {m : Nat} -> (g : Fin m) -> Gen MaybeEmpty $ Z f g
genZ_nfmg = deriveGen

genZ_n'fmg : Fuel -> (n : Nat) -> (f : Fin n) -> {m : Nat} -> (g : Fin m) -> Gen MaybeEmpty $ Z f g
genZ_n'fmg = deriveGen

genZ_n'fm'g : Fuel -> (n : Nat) -> (f : Fin n) -> (m : Nat) -> (g : Fin m) -> Gen MaybeEmpty $ Z f g
genZ_n'fm'g = deriveGen

genZ_nmfg : Fuel -> {n : Nat} -> {m : Nat} -> (f : Fin n) -> (g : Fin m) -> Gen MaybeEmpty $ Z f g
genZ_nmfg = deriveGen

genZ_mnfg : Fuel -> {m : Nat} -> {n : Nat} -> (f : Fin n) -> (g : Fin m) -> Gen MaybeEmpty $ Z f g
genZ_mnfg = deriveGen

genZ_mngf : Fuel -> {m : Nat} -> {n : Nat} -> (g : Fin m) -> (f : Fin n) -> Gen MaybeEmpty $ Z f g
genZ_mngf = deriveGen

genZ_mgnf : Fuel -> {m : Nat} -> (g : Fin m) -> {n : Nat} -> (f : Fin n) -> Gen MaybeEmpty $ Z f g
genZ_mgnf = deriveGen

genZ_mn_gf : Fuel -> {m : Nat} -> {n : Nat} -> Gen MaybeEmpty (g : Fin m ** f : Fin n ** Z f g)
genZ_mn_gf = deriveGen

genZ_n_mgf : Fuel -> {n : Nat} -> Gen MaybeEmpty (m ** g : Fin m ** f : Fin n ** Z f g)
genZ_n_mgf = deriveGen

genZ__mngf : Fuel -> Gen MaybeEmpty (m ** n ** g : Fin m ** f : Fin n ** Z f g)
genZ__mngf = deriveGen

genZ__nmgf : Fuel -> Gen MaybeEmpty (n ** m ** g : Fin m ** f : Fin n ** Z f g)
genZ__nmgf = deriveGen

genZ__mgnf : Fuel -> Gen MaybeEmpty (m ** g : Fin m ** n ** f : Fin n ** Z f g)
genZ__mgnf = deriveGen

---

-- should fail
genX_two_mngf : Fuel ->
                (Fuel -> {m : Nat} -> {n : Nat} -> (g : Fin m) -> (f : Fin n) -> Gen MaybeEmpty $ Z f g) =>
                (Fuel -> {m : Nat} -> {n : Nat} -> (g : Fin m) -> (f : Fin n) -> Gen MaybeEmpty $ Z f g) =>
                Gen MaybeEmpty X
genX_two_mngf = deriveGen

-- should fail
genX_mgnf_mngf : Fuel ->
                 (Fuel -> {m : Nat} -> (g : Fin m) -> {n : Nat} -> (f : Fin n) -> Gen MaybeEmpty $ Z f g) =>
                 (Fuel -> {m : Nat} -> {n : Nat} -> (g : Fin m) -> (f : Fin n) -> Gen MaybeEmpty $ Z f g) =>
                 Gen MaybeEmpty X
genX_mgnf_mngf = deriveGen

-- should not fail
genX_nf_mg_mngf : Fuel ->
                 (Fuel -> {n : Nat} -> (f : Fin n) -> Gen MaybeEmpty (m ** g : Fin m ** Z f g)) =>
                 (Fuel -> {m : Nat} -> {n : Nat} -> (g : Fin m) -> (f : Fin n) -> Gen MaybeEmpty $ Z f g) =>
                 Gen MaybeEmpty X
genX_nf_mg_mngf = deriveGen

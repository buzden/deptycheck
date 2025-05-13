import Deriving.DepTyCheck.Gen

%default total

data Y : Bool -> Nat -> Type where
  MkY1 : Y l n

data X : (b : _) -> Y (not b) n -> Type where
  MkX : X b MkY1

gen : Fuel -> (b : _) -> (n : _) -> (y : Y (not b) n) -> Gen0 $ X b y
gen = deriveGen

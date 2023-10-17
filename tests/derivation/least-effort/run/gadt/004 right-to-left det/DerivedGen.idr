module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X_GADT : Nat -> Nat -> Type where
  MkXG_4 : X_GADT 4 5
  MkXG_5 : X_GADT 5 m

Show (X_GADT n m) where
  show MkXG_4 = "MkXG_4"
  show MkXG_5 = "MkXG_5"

data X_ADT : Nat -> Nat -> Type where
  MkX : (n : _) -> (m : _) -> X_ADT n m

Show (X_ADT n m) where
  show $ MkX n m = "MkX \{show n} \{show m}"

data Y : Type where
  -- Should be generated left-to-right because of GADT on the left
  MkY_LR : X_GADT n m -> X_ADT n k -> Y
  -- Should be generated right-to-left because of GADT on the right
  MkY_RL : X_ADT n m -> X_GADT n k -> Y

Show Y where
  show $ MkY_LR g a = "MkY_LR (\{show g}) (\{show a})"
  show $ MkY_RL a g = "MkY_RL (\{show a}) (\{show g})"

checkedGen : Fuel -> Gen MaybeEmpty Y
checkedGen = deriveGen @{LeastEffort}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]

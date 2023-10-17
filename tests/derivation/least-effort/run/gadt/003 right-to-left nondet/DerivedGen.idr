module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X_GADT : Nat -> Nat -> Type where
  MkXG_4 : X_GADT 4 5
  MkXG_5 : {m : _} -> X_GADT 5 m

Show (X_GADT n m) where
  show MkXG_4       = "MkXG_4"
  show $ MkXG_5 {m} = "MkXG_5 \{show m}"

data Y : Type where
  MkY1 : X_GADT n m -> X_GADT n k -> Y
  MkY2 : X_GADT n m -> X_GADT k m -> Y

Show Y where
  show $ MkY1 l r = "MkY1 (\{show l}) (\{show r})"
  show $ MkY2 l r = "MkY2 (\{show l}) (\{show r})"

checkedGen : Fuel -> Gen MaybeEmpty Y
checkedGen = deriveGen @{LeastEffort}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]

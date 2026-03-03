module DerivedGen

import RunDerivedGen

%default total

data X : (b : Bool) -> (b = True) -> Type where
  XT : X True Refl
  XF : X True Refl

checkedGen : Fuel -> Gen MaybeEmpty (a ** b ** X a b)
checkedGen = deriveGen

Show (a ** b ** X a b) where
  show (True ** Refl ** XT) = "XT : X True Refl"
  show (True ** Refl ** XF) = "XF : X True Refl"
  show (False ** prf ** _) = absurd prf

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]

module DerivedGen

import RunDerivedGen

%default total

data X : (b : Bool) -> (if b then Unit else Nat) -> Type where
  XT : X True ()
  XF : X False n

checkedGen : Fuel -> Gen MaybeEmpty (a ** b ** X a b)
checkedGen = deriveGen

Show (a ** b ** X a b) where
  show (True ** () ** XT) = "XT : X True ()"
  show (False ** n ** XF) = "XF : X False \{show n}"

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]

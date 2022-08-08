module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data BoolP : Unit -> Type where
  TrueP : BoolP x
  FalseP : BoolP x

f : BoolP x -> Bool
f TrueP = True
f FalseP = False

Show (BoolP x) where
  show = show . f

data X : Type where
  MkX : (u : Unit) -> (x : BoolP u) -> So (f x) -> X

Show X where
  show (MkX () x prf) = "MkX () " ++ show x ++ " Oh"

checkedGen : Fuel -> Gen MaybeEmpty X
checkedGen = deriveGen

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]

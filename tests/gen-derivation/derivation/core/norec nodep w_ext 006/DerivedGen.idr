module DerivedGen

import public RunDerivedGen

%default total

%language ElabReflection

data X = MkX Bool

%runElab derive "X" [Generic, Meta, Show]

gensGen : Fuel -> Gen0 (a ** Gen0 a)
gensGen fuel = elements
  [ (String ** smallStrs fuel)
  , (Nat    ** smallNats fuel)
  ]

-- Check that demanding the gen of gens is allowed
checkedGen : Fuel -> (Fuel -> Gen0 (a ** Gen0 a)) => Gen0 X
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{gensGen} ]

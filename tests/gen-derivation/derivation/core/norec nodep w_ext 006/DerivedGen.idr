module DerivedGen

import public RunDerivedGen

%default total

%language ElabReflection

data X = MkX Bool

%runElab derive "X" [Generic, Meta, Show]

gensGen : Fuel -> Gen (a ** Gen a)
gensGen fuel = elements
  [ (String ** smallStrs fuel)
  , (Nat    ** smallNats fuel)
  ]

-- Check that demanding the gen of gens is allowed
checkedGen : Fuel -> (Fuel -> Gen (a ** Gen a)) => Gen X
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{gensGen} ]

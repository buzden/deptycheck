module DerivedGen

import public RunDerivedGen

%default total

%language ElabReflection

data X = MkX Bool

%runElab derive "X" [Generic, Meta, Show]

gensGen : Fuel -> (em : _) -> Gen CanBeEmptyStatic (a ** Gen em a)
gensGen fuel CanBeEmptyStatic = elements
  [ (String ** smallStrs fuel)
  , (Nat    ** smallNats fuel)
  ]
gensGen fuel _ = empty

-- Check that demanding the gen of gens is allowed
checkedGen : Fuel -> (Fuel -> (em : _) -> Gen CanBeEmptyStatic (a ** Gen em a)) => Gen CanBeEmptyStatic X
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{gensGen} ]

module DerivedGen

import public RunDerivedGen

%default total

%language ElabReflection

data X = MkX Bool

%hint
XShow : Show X
XShow = %runElab derive

gensGen : Fuel -> (em : _) -> Gen MaybeEmpty (a ** Gen em a)
gensGen fuel MaybeEmpty = elements
  [ (String ** smallStrs fuel)
  , (Nat    ** smallNats fuel)
  ]
gensGen fuel _ = empty

-- Check that demanding the gen of gens is allowed
checkedGen : Fuel -> (Fuel -> (em : _) -> Gen MaybeEmpty (a ** Gen em a)) => Gen MaybeEmpty X
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{gensGen} ]

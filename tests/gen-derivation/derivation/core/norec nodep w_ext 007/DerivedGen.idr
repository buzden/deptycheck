module DerivedGen

import public RunDerivedGen

%default total

%language ElabReflection

data X = MkX (Gen Bool)

Show X where
  show _ = #"an "X""#

gensGen : Fuel -> (a : Type) -> Gen $ Gen a
gensGen _ Bool = choiceMap (pure . pure) [True, False]
gensGen _ Nat  = choiceMap (pure . pure) [0 .. 99]
gensGen _ _    = empty

-- Check that demanding the gen of gens is allowed and is used
checkedGen : Fuel -> (Fuel -> (a : Type) -> Gen $ Gen a) => Gen X
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{gensGen} ]

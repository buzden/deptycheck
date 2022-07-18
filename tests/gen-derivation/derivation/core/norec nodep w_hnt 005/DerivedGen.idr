module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X = MkX Nat Nat

%runElab derive "X" [Generic, Meta, Show]

-- self-recursive type, should find the current generator instead of declared hint
%hint
hintedStringGen : Fuel -> Gen Nat
hintedStringGen _ = elements [2, 4, 8, 16]

-- shall use the hinted nats gen
export
checkedGen : Fuel -> Gen X
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl ]

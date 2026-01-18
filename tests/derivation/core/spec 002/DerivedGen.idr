module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X = MkX (Vect 3 Nat)

%hint
XShow : Show X
XShow = %runElab derive

export
checkedGen : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty X
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{smallNats} ]

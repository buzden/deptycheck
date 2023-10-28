module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X = MkX (Bool, Bool)

%hint
XShow : Show X
XShow = %runElab derive

export
checkedGen : Fuel -> Gen MaybeEmpty X
checkedGen = deriveGen

main : IO ()
main = runGs [ G checkedGen ]

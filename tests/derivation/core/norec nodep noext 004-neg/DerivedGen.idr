module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X = MkX Bool Void

%hint
XShow : Show X
XShow = %runElab derive

checkedGen : Fuel -> Gen MaybeEmpty X
checkedGen = deriveGen

main : IO ()
main = runGs [ G checkedGen ]

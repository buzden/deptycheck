module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X = MkX (Maybe String)

%hint
XShow : Show X
XShow = %runElab derive

export
checkedGen : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty X
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{smallStrs} ]

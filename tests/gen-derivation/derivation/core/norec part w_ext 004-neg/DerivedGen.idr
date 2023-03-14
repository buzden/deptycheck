module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

export
checkedGen : Fuel -> (Fuel -> Gen0 String) => Gen0 (Maybe String)
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{smallStrs} ]

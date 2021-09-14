module DerivedGen

import public Common

%default total

export
checkedGen : Fuel -> Gen (the Nat 0 = 1)
checkedGen fl = derivedGen fl 0 1

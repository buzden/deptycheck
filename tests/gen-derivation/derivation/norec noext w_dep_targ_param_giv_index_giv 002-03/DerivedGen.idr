module DerivedGen

import public Common

%default total

export
checkedGen : Fuel -> Gen (the Nat 18 = 18)
checkedGen fl = derivedGen fl 18 18

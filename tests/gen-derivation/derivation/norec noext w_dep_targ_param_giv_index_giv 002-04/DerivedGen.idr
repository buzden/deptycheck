module DerivedGen

import public Common

%default total

export
checkedGen : Fuel -> Gen (the Nat 18 = 0)
checkedGen fl = derivedGen fl 18 0

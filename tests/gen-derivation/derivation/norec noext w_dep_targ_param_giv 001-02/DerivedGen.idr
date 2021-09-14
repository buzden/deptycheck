module DerivedGen

import public Common

%default total

export
checkedGen : Fuel -> Gen (X True True)
checkedGen fl = derivedGen fl True True

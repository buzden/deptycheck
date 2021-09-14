module DerivedGen

import public Common

%default total

export
checkedGen : Fuel -> Gen (X True False)
checkedGen fl = derivedGen fl True False

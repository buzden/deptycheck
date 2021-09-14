module DerivedGen

import public Common

%default total

export
checkedGen : Fuel -> Gen (True = False)
checkedGen fl = derivedGen fl _ _

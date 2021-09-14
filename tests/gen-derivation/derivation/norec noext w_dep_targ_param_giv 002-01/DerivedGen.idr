module DerivedGen

import public Common

%default total

export
checkedGen : Fuel -> Gen (True = True)
checkedGen fl = derivedGen fl _ _

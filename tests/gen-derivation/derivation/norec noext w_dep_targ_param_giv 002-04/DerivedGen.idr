module DerivedGen

import public Common

%default total

export
checkedGen : Fuel -> Gen (False = True)
checkedGen fl = derivedGen fl _ _

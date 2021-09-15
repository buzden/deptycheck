module DerivedGen

import public Common

%default total

export
checkedGen : Fuel -> Gen (False = False)
checkedGen fl = derivedGen fl _ _

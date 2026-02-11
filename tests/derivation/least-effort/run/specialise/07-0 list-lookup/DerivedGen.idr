module DerivedGen

import RunDerivedGen

%default total


public export
data Lookup : a -> List (a, b) -> Type where
  Here : (y : b) -> Lookup x $ (x, y)::xys
  There : Lookup z xys -> Lookup z $ (x, y)::xys

Show a => Show b => Show (Lookup {a=a} {b=b} x xs) where
  showPrec d $ Here y = showCon d "Here" $ showArg y
  showPrec d $ There y = showCon d "There" $ showArg y

data UseLookup : Type where
  UL : Lookup True [(True, True, True, True)] -> UseLookup

Show UseLookup where
  showPrec d $ UL y = showCon d "UL" $ showArg y

checkedGen : Fuel -> Gen MaybeEmpty UseLookup
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO Unit
main = runGs [ G checkedGen ]

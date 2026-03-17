module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection


public export
data Lookup : a -> List (a, b) -> Type where
  Here : (y : b) -> Lookup x $ (x, y)::xys
  There : Lookup z xys -> Lookup z $ (x, y)::xys

data UseLookup : Type where
  UL : Lookup True [(True, True, True, True)] -> UseLookup

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty UseLookup

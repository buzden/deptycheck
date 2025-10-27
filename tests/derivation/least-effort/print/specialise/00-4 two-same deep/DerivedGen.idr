module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data Y = MkY (List Nat)

data X = MkX (List Nat) Y

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X

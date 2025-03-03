module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data ListNat : Type where
  Nil  : ListNat
  (::) : Nat -> ListNat -> ListNat

ProbabilityTuning `{DerivedGen.(::)}.dataCon where
  isConstructor = itIsConstructor
  tuneWeight _ = 1

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty ListNat

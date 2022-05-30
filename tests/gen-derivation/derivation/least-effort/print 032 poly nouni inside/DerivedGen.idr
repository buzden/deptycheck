module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data X = MkX (String, Nat, String)

%runElab printDerived @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen String) => (Fuel -> Gen Nat) => Gen X

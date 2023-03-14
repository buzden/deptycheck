module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data D : Bool -> Type where
  JJ : Nat ->    Nat -> D b
  FN : Nat ->    D b -> D False
  TL : String ->        D True
  TR : String -> D b -> D True

%runElab printDerived @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen0 Nat) => (Fuel -> Gen0 String) => (b : Bool) -> Gen0 $ D b

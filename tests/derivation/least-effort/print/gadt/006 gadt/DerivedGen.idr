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

%runElab printDerived @{LeastEffort} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => (Fuel -> Gen MaybeEmpty String) => (b : Bool) -> Gen MaybeEmpty $ D b

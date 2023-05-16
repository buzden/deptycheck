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

main : IO Unit
main = %runElab printDerived @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen Nat) => (Fuel -> Gen String) => Gen (b ** D b)

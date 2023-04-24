module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%language ElabReflection

data D : Bool -> Type where
  JJ : Nat ->    Nat -> D b
  FN : Nat ->    D b -> D False
  TL : String ->        D True
  TR : String -> D b -> D True

Show (D b) where
  show $ JJ n1 n2 = "JJ \{show n1} \{show n2}"
  show $ FN n d   = "FN \{show n} (\{show d})"
  show $ TL s     = "TL \{show s}"
  show $ TR s d   = "TR \{show s} (\{show d})"

checkedGen : Fuel -> (Fuel -> Gen CanBeEmptyStatic Nat) => (Fuel -> Gen CanBeEmptyStatic String) => (b : Bool) -> Gen CanBeEmptyStatic $ D b
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen @{smallNats} @{smallStrs} fl True
  , G $ \fl => checkedGen @{smallNats} @{smallStrs} fl False
  ]

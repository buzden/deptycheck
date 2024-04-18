module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

boolToNat : Bool -> Nat
boolToNat True  = 1
boolToNat False = 0

data X : Nat -> Type where
  X0 : X 0
  X1 : Bool -> X 1
  X2 : (x : Bool) -> X (boolToNat x)

%hint
XShow : Show $ X n
XShow = %runElab derive

checkedGen : Fuel -> (given : Nat) -> Gen MaybeEmpty $ X given
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl 0 ]

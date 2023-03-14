module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

ConstantUseTypeAlias : Bool -> Type
ConstantUseTypeAlias True  = Bool
ConstantUseTypeAlias False = Nat

data X : Type where
  X0 : X
  X1 : Bool -> X
  X2 : ConstantUseTypeAlias True -> ConstantUseTypeAlias False -> X

%runElab derive "X" [Generic, Meta, Show]

checkedGen : Fuel -> Gen0 X
checkedGen = deriveGen

main : IO ()
main = runGs [ G checkedGen ]

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

Show X where
  show X0 = "X0"
  show (X1 b) = "X1 \{show b}"
  show (X2 b n) = "X2 \{show b} \{show n}"

checkedGen : Fuel -> Gen MaybeEmpty X
checkedGen = deriveGen

main : IO ()
main = runGs [ G checkedGen ]

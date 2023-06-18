module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

NonReducibleUseTypeAlias : Bool -> Type
NonReducibleUseTypeAlias True  = Bool
NonReducibleUseTypeAlias False = Nat

data X : Type where
  X0 : X
  X1 : Bool -> X
  X2 : (b : Bool) -> NonReducibleUseTypeAlias b -> X

Show X where
  show X0           = "X0"
  show (X1 x)       = "X1 \{show x}"
  show (X2 True x)  = "X2 True \{show x}"
  show (X2 False x) = "X2 False \{show x}"

checkedGen : Fuel -> Gen MaybeEmpty X
checkedGen = deriveGen

main : IO ()
main = runGs [ G checkedGen ]

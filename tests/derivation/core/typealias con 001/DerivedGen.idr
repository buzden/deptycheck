module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

SimpleTypeAlias : Type
SimpleTypeAlias = Bool

data X : Type where
  X0 : X
  X1 : Bool -> X
  X2 : Bool -> SimpleTypeAlias -> X

%hint
XShow : Show X
XShow = %runElab derive

checkedGen : Fuel -> Gen MaybeEmpty X
checkedGen = deriveGen

main : IO ()
main = runGs [ G checkedGen ]

module DerivedGen

import RunDerivedGen

import Deriving.Show

%default total

%language ElabReflection

record X where
  constructor MkX
  field0  : Nat
  field1  : Nat
  field2  : Nat
  field3  : Nat
  field4  : Nat
  field5  : Nat
  field6  : Nat
  field7  : Nat
  field8  : Nat
  field9  : Nat
  field10 : Nat
  field11 : Nat

%hint ShowX : Show X; ShowX = %runElab derive

checkedGen : Fuel -> Gen MaybeEmpty X
checkedGen = deriveGen

main : IO ()
main = runGs [ G checkedGen ]

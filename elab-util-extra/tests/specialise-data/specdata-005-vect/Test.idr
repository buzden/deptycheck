module Test

import Shared

%language ElabReflection

%runElab specialiseData' (\n, a => Vect n a) "MyVect"

lN' : Unit
lN' = %runElab verifySpecialisation (Vect 0 Nat) (MyVect 0 Nat) [`([])]

l0 : List TTImp
l0 =
  [ `([0])
  , `([1])
  , `([2])
  ]

l0' : Unit
l0' = %runElab verifySpecialisation (Vect 1 Nat) (MyVect 1 Nat) l0

l1 : List TTImp
l1 =
  [ `(["a"])
  , `(["b"])
  ]

l1' : Unit
l1' = %runElab verifySpecialisation (Vect 1 String) (MyVect 1 String) l1

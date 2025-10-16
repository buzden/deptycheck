module Test

import Shared

%language ElabReflection

%runElab specialiseData' (\a => List a) "MyList"

l0 : List TTImp
l0 =
  [ `([])
  , `([0])
  , `([0, 1])
  ]

l0' : Unit
l0' = %runElab verifySpecialisation (List Nat) (MyList Nat) l0

l1 : List TTImp
l1 =
  [ `([])
  , `(["a"])
  , `(["a", "b"])
  ]

l1' : Unit
l1' = %runElab verifySpecialisation (List String) (MyList String) l1

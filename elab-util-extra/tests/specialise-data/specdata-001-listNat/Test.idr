module Test

import Shared

%language ElabReflection

%runElab specialiseData' (List Nat) "ListNat"

lnExprs : List TTImp
lnExprs =
  [ `([])
  , `([0])
  , `([0, 1])
  , `([1])
  , `([1, 2])
  , `([0, 1, 2])
  ]

lnVerify : Unit
lnVerify = %runElab verifySpecialisation (List Nat) ListNat lnExprs

failing "Can't find an implementation for FromString Nat"
  ln1 : ListNat
  ln1 = ["test"]

%runElab specialiseData' (List (List String)) "ListListString"

lssExprs : List TTImp
lssExprs =
  [ `([])
  , `([[]])
  , `([["Hello world"]])
  , `([[], ["x"]])
  , `([["y"], []])
  , `([["x", "y"], ["z"]])
  ]

lssVerify : Unit
lssVerify = %runElab verifySpecialisation (List (List String)) ListListString lssExprs

%runElab specialiseData' (List Type) "ListType"

ltExprs : List TTImp
ltExprs =
  [ `([])
  , `([Nat])
  , `([Nat, String])
  , `([Fin 1, Fin 2])
  ]

ltVerify : Unit
ltVerify = %runElab verifySpecialisation (List Type) ListType ltExprs

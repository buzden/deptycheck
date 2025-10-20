module Test

import Shared

%language ElabReflection

%runElab specialiseData' (List Nat) "ListNat"

--- Workaround for https://github.com/idris-lang/Idris2/issues/3651
ln' = %runElab verifySpecialisation (List Nat) ListNat
  [ `( [] )
  , `( [0] )
  , `( [0, 1] )
  , `( [1] )
  , `( [1, 2] )
  , `( [0, 1, 2] )
  ]

failing "Can't find an implementation for FromString Nat"
  ln1 : ListNat
  ln1 = ["test"]

%runElab specialiseData' (List (List String)) "ListListString"

--- Workaround for https://github.com/idris-lang/Idris2/issues/3651
lss' = %runElab verifySpecialisation (List (List String)) ListListString
  [ `( [] )
  , `( [[]] )
  , `( [[], []] )
  , `( [["Hello world"]] )
  , `( [[], ["x"]] )
  , `( [["y"], []] )
  , `( [["x", "y"], ["z"]] )
  ]

%runElab specialiseData' (List Type) "ListType"

--- Workaround for https://github.com/idris-lang/Idris2/issues/3651
lt' = %runElab verifySpecialisation (List Type) ListType
  [ `( [] )
  , `( [Nat] )
  , `( [Nat, String] )
  , `( [Fin 1, Fin 2] )
  ]

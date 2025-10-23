module Test

import Shared

%language ElabReflection

%runElab specialiseData' "ListNat" $ List Nat

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
ln' = %runElab verifySpecialisation (List Nat) ListNat
  [ `( [] )
  , `( [0] )
  , `( [0, 1] )
  , `( [1] )
  , `( [1, 2] )
  , `( [0, 1, 2] )
  ]

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
ln'' = %runElab verifyInvalidConstructors (List Nat) ListNat
  [ `( ["x"] )
  , `( ["x", "y", "z"] )
  ]

failing "Can't find an implementation for FromString Nat"
  ln1 : ListNat
  ln1 = ["test"]

%runElab specialiseData' "ListListString" (List (List String))

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
lss' = %runElab verifySpecialisation (List (List String)) ListListString
  [ `( [] )
  , `( [[]] )
  , `( [[], []] )
  , `( [["Hello world"]] )
  , `( [[], ["x"]] )
  , `( [["y"], []] )
  , `( [["x", "y"], ["z"]] )
  ]

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
lss'' = %runElab verifyInvalidConstructors (List (List String)) ListListString
  [ `( ["x"] )
  , `( [[1,2],[3,4]] )
  ]

%runElab specialiseData' "ListType" (List Type)

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
lt' = %runElab verifySpecialisation (List Type) ListType
  [ `( [] )
  , `( [Nat] )
  , `( [Nat, String] )
  , `( [Fin 1, Fin 2] )
  ]

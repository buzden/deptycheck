module Test

import Shared

%language ElabReflection

%runElab specialiseData' (\a => List a) "MyList"

--- Workaround for https://github.com/idris-lang/Idris2/issues/3651
l0' = %runElab verifySpecialisation (List Nat) (MyList Nat)
  [ `( [] )
  , `( [0] )
  , `( [0, 1] )
  ]

--- Workaround for https://github.com/idris-lang/Idris2/issues/3651
l1' = %runElab verifySpecialisation (List String) (MyList String)
  [ `( [] )
  , `( ["a"] )
  , `( ["a", "b"] )
  ]


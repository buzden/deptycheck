module Test

import Shared

%language ElabReflection

%runElab specialiseDataLam' "MyList" $ \a => List a

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
l0' = %runElab verifySpecialisation (List Nat) (MyList Nat)
  [ `( [] )
  , `( [0] )
  , `( [0, 1] )
  ]

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
l0'' = %runElab verifyInvalidConstructors (List Nat) (MyList Nat)
  [  `( ["a"] )
  , `( ["a", "b"] )
  ]

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
l1' = %runElab verifySpecialisation (List String) (MyList String)
  [ `( [] )
  , `( ["a"] )
  , `( ["a", "b"] )
  ]

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
l1'' = %runElab verifyInvalidConstructors (List String) (MyList String)
  [ `( [0] )
  , `( [0, 1] )
  ]

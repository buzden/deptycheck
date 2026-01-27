module Test

import Shared

%language ElabReflection

%runElab specialiseDataLam' "ListVectNat" $ \a => List $ Vect a Nat

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
lvn0' = %runElab verifySpecialisation (List $ Vect 0 Nat) (ListVectNat 0)
  [ `( [] )
  , `( [[]] )
  , `( [[], []] )
  ]

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
lvn0'' = %runElab verifyInvalidConstructors (List $ Vect 0 Nat) (ListVectNat 0)
  [ `( [[0]] )
  , `( [[1,2], [3,4]] )
  ]

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
lvn1' = %runElab verifySpecialisation (List $ Vect 1 Nat) (ListVectNat 1)
  [ `( [] )
  , `( [[0]] )
  , `( [[1]] )
  , `( [[0], [1]] )
  ]

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
lvn1'' = %runElab verifyInvalidConstructors (List $ Vect 1 Nat) (ListVectNat 1)
  [ `( [[]] )
  , `( [[1,2], [3,4]] )
  ]

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
lvn2' = %runElab verifySpecialisation (List $ Vect 2 Nat) (ListVectNat 2)
  [ `( [] )
  , `( [[0, 1]] )
  , `( [[2, 3]] )
  , `( [[4, 5], [6, 7]] )
  ]

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
lvn2'' = %runElab verifyInvalidConstructors (List $ Vect 2 Nat) (ListVectNat 2)
  [ `( [[]] )
  , `( [[0]] )
  ]

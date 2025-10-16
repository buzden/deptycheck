module Test

import Shared

%language ElabReflection

%runElab specialiseData' (\a => List $ Vect a Nat) "ListVectNat"

lvn0Exprs : List TTImp
lvn0Exprs =
  [ `([])
  , `([[]])
  , `([[], []])
  ]

lvn0' : Unit
lvn0' = %runElab verifySpecialisation (List $ Vect 0 Nat) (ListVectNat 0) lvn0Exprs

lvn1Exprs : List TTImp
lvn1Exprs =
  [ `([])
  , `([[0]])
  , `([[1]])
  , `([[0], [1]])
  ]

lvn1' : Unit
lvn1' = %runElab verifySpecialisation (List $ Vect 1 Nat) (ListVectNat 1) lvn1Exprs


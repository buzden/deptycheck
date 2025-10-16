module Test

import Shared

%language ElabReflection

data X : (Nat -> Type) -> Type where
  X5 : t 5 -> X t
  Xn : t n -> X t

%runElab specialiseData' (X Fin) "XFin"

x0 : List TTImp
x0 =
  [ `(X5 0)
  , `(X5 1)
  , `(X5 2)
  , `(X5 3)
  , `(X5 4)
  , `(Xn (the (Fin 2) 0))
  , `(Xn (the (Fin 6) 3))
  ]

x0' : Unit
x0' = %runElab verifySpecialisation (X Fin) XFin x0

%runElab specialiseData' (X (\n => Vect n Nat)) "XVNat"

x1 : List TTImp
x1 =
  [ `(X5 [1,2,3,4,5])
  , `(X5 [6,7,8,9,10])
  , `(Xn [])
  , `(Xn [1])
  , `(Xn [2,3])
  ]

x1' : Unit
x1' = %runElab verifySpecialisation (X (\n => Vect n Nat)) XVNat x1

%runElab specialiseData' (X (\n => Vect n $ Fin n)) "XVFin"

x2 : List TTImp
x2 =
  [ `(X5 [0,1,2,3,4])
  , `(X5 [4,3,2,1,0])
  , `(X5 [0,4,1,3,2])
  , `(Xn [0,1,2])
  , `(Xn [0])
  , `(Xn [])
  ]

x2' : Unit
x2' = %runElab verifySpecialisation (X (\n => Vect n $ Fin n)) XVFin x2

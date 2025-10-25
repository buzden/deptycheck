module Test

import Shared

%language ElabReflection

data X : (Nat -> Type) -> Type where
  X5 : t 5 -> X t
  Xn : t n -> X t

%runElab specialiseData' "XFin" $ X Fin

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
x0' = %runElab verifySpecialisation (X Fin) XFin
  [ `(X5 0)
  , `(X5 1)
  , `(X5 2)
  , `(X5 3)
  , `(X5 4)
  , `(Xn (the (Fin 2) 0))
  , `(Xn (the (Fin 6) 3))
  ]

%runElab specialiseData' "XVNat" $ X (\n => Vect n Nat)

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
x1' = %runElab verifySpecialisation (X (\n => Vect n Nat)) XVNat
  [ `(X5 [1,2,3,4,5])
  , `(X5 [6,7,8,9,10])
  , `(Xn [])
  , `(Xn [1])
  , `(Xn [2,3])
  ]


%runElab specialiseData' "XVFin" $ X (\n => Vect n $ Fin n)

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
x2' = %runElab verifySpecialisation (X (\n => Vect n $ Fin n)) XVFin
  [ `(X5 [0,1,2,3,4])
  , `(X5 [4,3,2,1,0])
  , `(X5 [0,4,1,3,2])
  , `(Xn [0,1,2])
  , `(Xn [0])
  , `(Xn [])
  ]

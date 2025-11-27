module Test

import Shared

%language ElabReflection

%runElab specialiseDataLam' "Fin0" $ Fin 0

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e0' = %runElab verifySpecialisation (Fin 0) Fin0 []

e0NoCons : Fin0 -> Nat
e0NoCons _ impossible

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e0'' = %runElab verifyEmptyType (Fin 0) Fin0


%runElab specialiseDataLam' "Fin1" $ Fin 1

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e1' = %runElab verifySpecialisation (Fin 1) Fin1
  [ `( FZ )
  ]

%runElab specialiseDataLam' "Fin2" $ Fin 2

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e2' = %runElab verifySpecialisation (Fin 2) Fin2
  [ `( FZ )
  , `( FS FZ ) -- TODO: Implement non-Num fromInteger auto-derivation
  ]



module Test

import Shared

%language ElabReflection

%runElab specialiseData' (\a => Maybe $ Fin a) "MFin"

mFin0NoJust : MFin 0 -> Unit
mFin0NoJust (Nothing) = MkUnit
mFin0NoJust (Just _) impossible

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
mf0' = %runElab verifySpecialisation (Maybe (Fin 0)) (MFin 0) [`(Nothing)]

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
mf1' = %runElab verifySpecialisation (Maybe (Fin 1)) (MFin 1)
  [ `( Nothing )
  , `( Just 0 )
  ]

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
mf2v = %runElab verifySpecialisation (Maybe (Fin 2)) (MFin 2)
  [ `( Nothing )
  , `( Just 0 )
  , `( Just 1 )
  ]

failing "Sorry, I can't find any elaboration which works."
  mFinDecEq1 : (decEq (Nothing 10) (Nothing 4)) = Yes ?
  mFinDecEq1 = Refl


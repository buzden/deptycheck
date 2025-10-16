module Test

import Shared

%language ElabReflection

%runElab specialiseData' (\a => Maybe $ Fin a) "MFin"

mFin0Vals : List TTImp
mFin0Vals = [`(Nothing)]

mFin0NoJust : MFin 0 -> Unit
mFin0NoJust (Nothing) = MkUnit
mFin0NoJust (Just _) impossible

mf0v : Unit
mf0v = %runElab verifySpecialisation (Maybe (Fin 0)) (MFin 0) mFin0Vals

mFin1Vals : List TTImp
mFin1Vals =
  [ `(Nothing)
  , `(Just 0)
  ]

mf1v : Unit
mf1v = %runElab verifySpecialisation (Maybe (Fin 1)) (MFin 1) mFin1Vals

mFin2Vals : List TTImp
mFin2Vals =
  [ `(Nothing)
  , `(Just 0)
  , `(Just 1)
  ]

mf2v : Unit
mf2v = %runElab verifySpecialisation (Maybe (Fin 2)) (MFin 2) mFin2Vals

failing "Sorry, I can't find any elaboration which works."
  mFinDecEq1 : (decEq (Nothing 10) (Nothing 4)) = Yes ?
  mFinDecEq1 = Refl


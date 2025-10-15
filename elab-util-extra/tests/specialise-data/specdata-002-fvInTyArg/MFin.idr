module MFin

import Shared

%language ElabReflection

%runElab specialiseData' (\a => Maybe $ Fin a) "MFin"

mFin0 : MFin 10
mFin0 = Nothing 10

mFin1 : MFin 5
mFin1 = Just 5 2

mFinCast0 : List $ Maybe $ Fin 10
mFinCast0 = cast <$> [ Nothing 10, Just 10 1]

mFinCast0' : MFin.mFinCast0 = [Nothing, Just 1]
mFinCast0' = Refl

mFinCast1 : List $ MFin 10
mFinCast1 = cast <$> [the (Maybe $ Fin 10) Nothing, the (Maybe $ Fin 10) (Just 5)]

mFinCast1' : MFin.mFinCast1 = [Nothing 10, Just 10 5]
mFinCast1' = Refl

mFinDecEq0 : (decEq (Nothing 10) (Nothing 10)) = Yes ?
mFinDecEq0 = Refl

failing
  mFinDecEq1 : (decEq (Nothing 10) (Nothing 4)) = Yes ?
  mFinDecEq1 = Refl

mFinDecEq1 : (decEq (Nothing 7) (Just 7 3)) = No ?
mFinDecEq1 = Refl

mFinDecEq2 : (decEq (Just 7 4) (Just 7 3)) = No ?
mFinDecEq2 = Refl

mFinDecEq3 : (decEq (Just 7 4) (Just 7 4)) = Yes ?
mFinDecEq3 = Refl

mFinEq0 : (Nothing 5 == Nothing 5) = True
mFinEq0 = Refl

mFinEq1 : (Just 5 3 == Nothing 5) = False
mFinEq1 = Refl

mFinEq2 : (Just 5 3 == Just 5 2) = False
mFinEq2 = Refl

mFinEq3 : (Just 5 4 == Just 5 4) = True
mFinEq3 = Refl

mFinNEq0 : (Nothing 5 /= Nothing 5) = False
mFinNEq0 = Refl

mFinNEq1 : (Just 5 3 /= Nothing 5) = True
mFinNEq1 = Refl

mFinNEq2 : (Just 5 3 /= Just 5 2) = True
mFinNEq2 = Refl

mFinNEq3 : (Just 5 4 /= Just 5 4) = False
mFinNEq3 = Refl

%runElab logMsg "" 0 $ show $ Nothing 10
%runElab logMsg "" 0 $ show $ Just 10 8



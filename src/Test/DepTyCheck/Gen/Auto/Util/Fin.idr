module Test.DepTyCheck.Gen.Auto.Util.Fin

import public Data.Vect

%default total

public export
allFins' : (n : Nat) -> Vect n (Fin n)
allFins' Z     = []
allFins' (S k) = FZ :: map FS (allFins' k)

public export
rangeFrom0To : Fin n -> List (Fin n)
rangeFrom0To FZ     = [FZ]
rangeFrom0To (FS x) = FZ :: (FS <$> rangeFrom0To x)

public export
rangeFromTo : Fin n -> Fin n -> List (Fin n)
rangeFromTo FZ     FZ     = [FZ]
rangeFromTo FZ     r      = rangeFrom0To r
rangeFromTo l      FZ     = reverse $ rangeFrom0To l
rangeFromTo (FS l) (FS r) = FS <$> rangeFromTo l r

public export
tryToFit : {to : _} -> Fin from -> Maybe $ Fin to
tryToFit {to=0}   _      = Nothing
tryToFit {to=S _} FZ     = Just FZ
tryToFit {to=S _} (FS x) = FS <$> tryToFit x

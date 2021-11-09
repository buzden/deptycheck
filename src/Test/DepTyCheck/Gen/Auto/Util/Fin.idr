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

export
allGreaterThan : {n : _} -> Fin n -> List (Fin n)
allGreaterThan curr = case strengthen $ FS curr of
                        Nothing => []
                        Just next => next :: allGreaterThan (assert_smaller curr next) -- `next` is closer to the upper bound than `curr`

public export
tryToFit : {to : _} -> Fin from -> Maybe $ Fin to
tryToFit {to=0}   _      = Nothing
tryToFit {to=S _} FZ     = Just FZ
tryToFit {to=S _} (FS x) = FS <$> tryToFit x

public export
weakenToSuper : {i : Fin n} -> Fin (finToNat i) -> Fin n
weakenToSuper {i = FS _} FZ     = FZ
weakenToSuper {i = FS _} (FS x) = FS $ weakenToSuper x

export
weakenToSuper_correct : {i : Fin n} -> (x : Fin $ finToNat i) -> finToNat (weakenToSuper {i} x) = finToNat x
weakenToSuper_correct {i = FS _} FZ     = Refl
weakenToSuper_correct {i = FS _} (FS x) = cong S $ weakenToSuper_correct x

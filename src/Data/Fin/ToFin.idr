||| Conversions of `Fin`s to `Fin`s
module Data.Fin.ToFin

import public Data.Fin

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

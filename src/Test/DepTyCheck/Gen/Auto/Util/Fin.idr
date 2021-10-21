module Test.DepTyCheck.Gen.Auto.Util.Fin

import public Data.Vect

%default total

public export
allFins' : (n : Nat) -> Vect n (Fin n)
allFins' Z     = []
allFins' (S k) = FZ :: map FS (allFins' k)

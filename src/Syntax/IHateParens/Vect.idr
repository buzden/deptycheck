module Syntax.IHateParens.Vect

import public Data.Vect

%default total

public export %inline
(.asList) : Vect n a -> List a
(.asList) = toList

public export
(.withIdx) : (xs : Vect n a) -> Vect n (Fin n, a)
(.withIdx) []      = []
(.withIdx) (x::xs) = (FZ, x) :: (xs.withIdx <&> mapFst FS)

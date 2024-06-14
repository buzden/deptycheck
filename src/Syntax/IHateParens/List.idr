module Syntax.IHateParens.List

import Data.Vect

%default total

public export %inline
(.length) : List a -> Nat
xs.length = length xs

public export %inline
(.asVect) : (xs : List a) -> Vect xs.length a
xs.asVect = fromList xs

public export
(.withIdx) : (xs : List a) -> List (Fin xs.length, a)
(.withIdx) []      = []
(.withIdx) (x::xs) = (FZ, x) :: (xs.withIdx <&> mapFst FS)

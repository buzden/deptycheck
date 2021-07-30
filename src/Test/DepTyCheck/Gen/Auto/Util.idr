module Test.DepTyCheck.Gen.Auto.Util

import Data.Fin

%default total

--- Lists utilities ---

public export %inline
(.length) : List a -> Nat
xs.length = length xs

-- Not effective but clean
public export
find' : (p : a -> Bool) -> (xs : List a) -> Maybe $ Fin xs.length
find' _ [] = Nothing
find' p (x::xs) = if p x then Just FZ else FS <$> find' p xs

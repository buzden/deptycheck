module Data.List.Lookup

%default total

-----------------------------------------------
--- List lookup with propositional equality ---
-----------------------------------------------

public export
data Lookup : a -> List (a, b) -> Type where
  Here : (y : b) -> Lookup x $ (x, y)::xys
  There : Lookup z xys -> Lookup z $ (x, y)::xys

public export
reveal : Lookup {b} x xys -> b
reveal (Here y) = y
reveal (There subl) = reveal subl

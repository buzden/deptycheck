module DepsCheck

export
listToCheck : List Type
listToCheck =
  [ ({a : Type} -> (xs : List a) -> (v : List a) -> (0 _ : case v of [] => Unit; (y::ys) => Void) -> Nat)
  , ({a : Type} -> (xs : List a) -> (v : List a) -> (0 _ : case v of [] => Unit; (x::xs) => Void) -> Nat)
  ]

module DepsCheck

export
listToCheck : List Type
listToCheck =
  [ ((x : Nat) -> (\x => S x) = S -> Unit) -- which of two `x`'s would be resolved in `S x`?
  --, ({a : Type} -> (xs : List a) -> (v : List a) -> (case v of [] => Unit; (x::xs) => Void) -> Nat)
  ]

module DepsCheck

export
listToCheck : List Type
listToCheck =
  [ ((x : Nat) -> (\x => S x) = S -> Unit) -- which of two `x`'s would be resolved in `S x`?
  , ((x : Nat) -> (\x : Nat => \x : Nat => S x) = (\x : Nat => S) -> Unit)
  , ((x : Nat) -> (\y => S y) = S -> Unit)
  --, ({a : Type} -> (xs : List a) -> (v : List a) -> (case v of [] => Unit; (x::xs) => Void) -> Nat)
  ]

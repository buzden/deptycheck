module DepsCheck

export
listToCheck : List Type
listToCheck =
  [ ((x : Nat) -> (\x => S x) = S -> Unit)
  , ((x : Nat) -> (\x : Nat => \x : Nat => S x) = (\x : Nat => S) -> Unit)
  , ((x : Nat) -> (\y => S y) = S -> Unit)
  ]

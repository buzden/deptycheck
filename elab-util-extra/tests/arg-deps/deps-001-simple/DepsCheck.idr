module DepsCheck

export
listToCheck : List Type
listToCheck =
  [ Unit
  , (Nat -> Nat)
  , (Nat -> Nat -> Nat)
  , ({a : Type} -> List a -> Nat)
  ]

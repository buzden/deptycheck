module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X : Nat -> Type where
  L : X n
  N : (k : Nat) -> X k -> X n -> X (S n)

GenOrderTuning `{N}.dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [`{k}]

checkedGen : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => (n : Nat) -> Gen MaybeEmpty (X n)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

Show (X n) where
  show x = "size \{show $ size x}" where
    size : forall n. X n -> Nat
    size L         = 1
    size (N _ l r) = 1 + size l + size r

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl @{const $ elements [0, 1]} 0
  , G $ \fl => checkedGen fl @{const $ elements [0, 1]} 1
  , G $ \fl => checkedGen fl @{const $ elements [0, 1]} 2
  ]

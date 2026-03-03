module DerivedGen

import RunDerivedGen

%default total

data X : Type -> Type where
  MkX : Nat -> List a -> X a

checkedGen : Fuel -> (Fuel -> Gen MaybeEmpty (t ** List t)) => Gen MaybeEmpty (t ** X t)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

genList : Fuel -> Gen MaybeEmpty (t ** List t)
genList _ = elements' {f=List} [ (Nat ** [1, 2, 3]), (Bool ** [True, False]), (List Nat ** [[], [1, 2, 3]]) ]

Show (t ** X t) where
  show (Nat ** MkX n xs) = show "MkX \{show n} \{show xs}"
  show (Bool ** MkX n xs) = show "MkX \{show n} \{show xs}"
  show (_ ** MkX n xs) = show "MkX \{show n} (? if length \{show $ length xs})"

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl @{genList}
  ]

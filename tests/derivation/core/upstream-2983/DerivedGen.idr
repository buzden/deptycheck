module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data VectMaybeAnyType : Nat -> Type where
  Nil  : VectMaybeAnyType Z
  (::) : Bool -> VectMaybeAnyType n -> VectMaybeAnyType (S n)

data AtIndex : (n : Nat) -> Bool -> VectMaybeAnyType n -> Type where
  Here  : AtIndex (S n) x (x::xs)

Show (AtIndex n v xs) where
  show _ = "Here"

checkedGen : Fuel -> (n : Nat) -> (b : Bool) -> (v : VectMaybeAnyType n) -> Gen MaybeEmpty $ AtIndex n b v
checkedGen = deriveGen @{LeastEffort}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 3 True  [ False, True, True ]
  , G $ \fl => checkedGen fl 3 False [ False, True, True ]
  ]

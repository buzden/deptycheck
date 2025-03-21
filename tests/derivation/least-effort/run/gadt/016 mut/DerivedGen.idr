module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data ListNat : Type
data Constraint : Nat -> ListNat -> Type

data ListNat : Type where
  Nil  : ListNat
  (::) : (x : Nat) -> (xs : ListNat) -> Constraint x xs => ListNat

data Constraint : Nat -> ListNat -> Type where
  Empty    : Constraint e []
  NonEmpty : Constraint e $ (x::xs) @{prf}
  Any1     : Constraint e xs
  Any2     : Constraint e xs
  Any3     : Constraint e xs

checkedGen : Fuel -> Gen MaybeEmpty ListNat
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

Show ListNat where
  show = show . toList where
    toList : ListNat -> List Nat
    toList []      = []
    toList (x::xs) = x :: toList xs

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]

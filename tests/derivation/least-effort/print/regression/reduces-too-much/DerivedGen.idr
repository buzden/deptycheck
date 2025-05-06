module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

data ListNat : Type
data Constraint : Nat -> ListNat -> Type

namespace Hide
  export
  f : ListNat -> ListNat
  f = id

data ListNat : Type where
  Nil  : ListNat
  (::) : (x : Nat) -> (xs : ListNat) -> Constraint x (f xs) => ListNat

data Constraint : Nat -> ListNat -> Type where
  Empty    : Constraint e []
  NonEmpty : Constraint e $ (x::xs) @{prf}
  Any1     : Constraint e xs
  Any2     : Constraint e xs
  Any3     : Constraint e xs

length : ListNat -> Nat
length []      = Z
length (_::xs) = S $ length xs

%language ElabReflection

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty ListNat

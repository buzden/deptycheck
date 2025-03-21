module DerivedGen

import Deriving.DepTyCheck.Gen

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

%language ElabReflection

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty ListNat

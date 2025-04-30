module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

%hint DA : DeriveBodyForCon; DA = LeastEffort

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

listNats : Fuel -> Gen MaybeEmpty ListNat
listNats = deriveGen

-- Check that length of generated lists is uniformly distributed

mainFor : (depth : Nat) -> IO ()
mainFor depth = printVerdict (listNats $ limit depth) $ fromList
                  $ [ coverWith (ratio 1 $ S depth) ((== n) . length) | n <- [0 .. depth] ]

main : IO ()
main = do
  mainFor 2
  mainFor 5
  mainFor 10

module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

%hint DA : ConstructorDerivator; DA = LeastEffort

data ListNat : Type
data Constraint : ListNat -> Type

data ListNat : Type where
  Nil  : ListNat
  (::) : Nat -> (xs : ListNat) -> Constraint xs => ListNat

data Constraint : ListNat -> Type where
  Empty    : Constraint []
  NonEmpty : Constraint $ (x::xs) @{prf}

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

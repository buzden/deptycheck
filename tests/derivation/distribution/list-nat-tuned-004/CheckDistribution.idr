module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

%language ElabReflection

data ListNat : Type where
  Nil  : ListNat
  (::) : Nat -> ListNat -> ListNat

length : ListNat -> Nat
length []      = Z
length (_::xs) = S $ length xs

ProbabilityTuning `{CheckDistribution.Nil}.dataCon where
  isConstructor = itIsConstructor
  tuneWeight = const 2

listNats : Fuel -> Gen MaybeEmpty ListNat
listNats = deriveGen

----------------------

p : (fuel, currLen : Nat) -> Probability
p n k = if k <= n then P $ roughlyFit $ 2.0 * cast (n + 1 `minus` k) / cast ((n + 1) * (n + 2)) else 0

mainFor : (depth : Nat) -> IO ()
mainFor depth = printVerdict (listNats $ limit depth) $ fromList $ [ coverWith (p depth n) ((== n) . length) | n <- [0 .. depth + 1] ]

main : IO ()
main = do
  mainFor 0
  mainFor 1
  mainFor 2
  mainFor 5

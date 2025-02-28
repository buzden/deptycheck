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

ProbabilityTuning `{CheckDistribution.(::)}.dataCon where
  isConstructor = itIsConstructor
  tuneWeight = (*2)

listNats : Fuel -> Gen MaybeEmpty ListNat
listNats = deriveGen

----------------------

pow2 : Nat -> Double
pow2 k = pow 2.0 $ cast k

%hide List.Lazy.rangeFromTo
%hide List.Lazy.rangeFromThenTo

fac : Nat -> Double
fac 0 = 1
fac n = cast $ product [1 .. n]

-- (2 * n + 1)!!, i.e. 2 * 4 * 6 * ... * (2*n+1)
oddFacFac : Nat -> Double
oddFacFac n = cast $ product [1, 3 .. 2*n+1]

p : (fuel, currLen : Nat) -> Probability
p n k = if k <= n then P $ roughlyFit $ (pow2 k * fac n * oddFacFac ((n `minus` k) `minus` 1)) / (fac (n `minus` k) * oddFacFac n) else 0

mainFor : (depth : Nat) -> IO ()
mainFor depth = printVerdict (listNats $ limit depth) $ fromList $ [ coverWith (p depth n) ((== n) . length) | n <- [0 .. depth + 1] ]

main : IO ()
main = do
  mainFor 0
  mainFor 1
  mainFor 2
  mainFor 5

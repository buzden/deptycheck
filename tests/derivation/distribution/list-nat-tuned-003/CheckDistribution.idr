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
  tuneWeight = \_ => 4

ProbabilityTuning `{CheckDistribution.Nil}.dataCon where
  isConstructor = itIsConstructor
  tuneWeight = const 4

listNats : Fuel -> Gen MaybeEmpty ListNat
listNats = deriveGen

----------------------

pow2 : Nat -> Double
pow2 k = pow 2.0 $ cast k

p : (fuel, currLen : Nat) -> Probability
p n k = case compare n k of
  GT => P $ roughlyFit $ 1 / pow2 (1+k)
  EQ => P $ roughlyFit $ 1 / pow2 k
  LT => 0

mainFor : (depth : Nat) -> IO ()
mainFor depth = printVerdict (listNats $ limit depth) $ fromList $ [ coverWith (p depth n) ((== n) . length) | n <- [0 .. depth + 1] ]

main : IO ()
main = do
  mainFor 0
  mainFor 1
  mainFor 2
  mainFor 5

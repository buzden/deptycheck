module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

%language ElabReflection

%hint DA : ConstructorDerivator; DA = LeastEffort

data VectNat : Nat -> Type where
  Nil  : VectNat Z
  (::) : Nat -> VectNat n -> VectNat (S n)

index : Fin n -> VectNat n -> Nat
index FZ     (x::_ ) = x
index (FS k) (_::xs) = index k xs

vectNats : Fuel -> (Fuel -> Gen Nat) => (n : Nat) -> Gen $ VectNat n
vectNats = deriveGen

nats : Fuel -> Gen Nat
nats = deriveGen

-- Check that every number in every position is uniformly distributed

mainFor : (len : Nat) -> (depth : Nat) -> IO ()
mainFor len depth = printVerdict (vectNats @{nats} (limit depth) len) $ fromList
                      [ coverWith (ratio 1 (S depth)) ((== n) . index idx) | n <- [0 .. depth], idx <- allFins len ]

-- NOTE: A separate test is when for this derived generator we pass `depth` test.
--       Now, since we still spend fuel even when `given` argument descreases, when we set high `len` > `depth`,
--       no statistics can be searched for.

main : IO ()
main = do
  mainFor 1 4
  mainFor 4 5
  mainFor 8 10

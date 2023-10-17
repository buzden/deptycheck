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

index : Nat -> ListNat -> Maybe Nat
index _     []      = Nothing
index Z     (x::_ ) = Just x
index (S k) (_::xs) = index k xs

listNats : Fuel -> Gen MaybeEmpty ListNat
listNats = deriveGen

-- Check that every number in every position is uniformly distributed (with the correction on the length of the list)

mainFor : (depth : Nat) -> IO ()
mainFor depth = printVerdict (listNats $ limit depth) $ fromList
                  $  [ coverWith (ratio 1 $ S depth) ((== n) . length) | n <- [0 .. depth] ]
                  ++ [ coverWith (ratio @{believe_me $ LTEZero {right=Z}} @{believe_me $ ItIsSucc {n=Z}}
                         (depth `minus` idx) (S depth * S depth)) ((== Just n) . index idx)
                     | n <- [0 .. depth], idx <- [1, 2 .. depth] <&> (`minus` 1) ]

main : IO ()
main = do
  mainFor 0
  mainFor 1
  mainFor 2
  mainFor 5

module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

%language ElabReflection

nats : Fuel -> Gen MaybeEmpty Nat
nats = deriveGen

mainFor : (depth : Nat) -> IO ()
mainFor depth = printVerdict (nats $ limit depth) $ fromList [0 .. depth] <&> \n => coverWith (ratio 1 (S depth)) (== n)

main : IO ()
main = do
  mainFor 0
  mainFor 1
  mainFor 2
  mainFor 10
  mainFor 20

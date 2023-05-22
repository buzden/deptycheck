module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

nats : (n : Nat) -> Gen MaybeEmpty Nat
nats n = elements [1 .. n]

genFin : (n : Nat) -> Gen MaybeEmpty $ Fin n
genFin Z     = empty
genFin (S n) = elements' $ forget $ allFins n

genAnyFin : Gen MaybeEmpty Nat => Gen MaybeEmpty (n ** Fin n)
genAnyFin @{genNat} = do
  n <- forgetAlternatives genNat
  f <- genFin n
  pure (n ** f)

mainFor : Nat -> IO ()
mainFor Z = pure ()
mainFor n@(S k) = do
  printVerdict (genAnyFin @{nats n}) $ fromList $
    [ coverWith (ratio 1 n) ((== S n') . fst) | n' <- [0 .. k] ]
  printVerdict (genAnyFin @{nats n}) $ fromList $
    [ coverWith (ratio 1 n * ratio 1 (S n')) (== (S n' ** f)) | n' <- [0 .. k], f <- forget $ allFins n']

main : IO ()
main = do
  mainFor 0
  mainFor 1
  mainFor 2
  mainFor 4
  mainFor 8

module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

nats : (n : Nat) -> Gen MaybeEmpty Nat
nats n = elements' [1 .. n]

genFin : (n : Nat) -> Gen MaybeEmpty $ Fin n
genFin Z     = empty
genFin (S n) = elements' $ forget $ allFins n

genAnyFin : Gen MaybeEmpty Nat => Gen MaybeEmpty (n ** Fin n)
genAnyFin @{genNat} = oneOf $ do
  n <- alternativesOf genNat
  f <- alternativesOf $ genFin n
  pure (n ** f)

mainFor : Nat -> IO ()
mainFor Z     = pure ()
mainFor (S k) = do
  let genCt@(S _) = (S k * S (S k)) `div` 2
    | _ => pure ()
  let p = ratio 1 genCt
  printVerdict (genAnyFin @{nats $ S k}) $ fromList $
    [coverWith p (== (S n' ** f)) | n' <- [0 .. k], f <- forget $ allFins n']

main : IO ()
main = do
  mainFor 0
  mainFor 1
  mainFor 2
  mainFor 4
  mainFor 8

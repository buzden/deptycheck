module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

nats : (n : Nat) -> Gen0 Nat
nats n = elements [1 .. n]

genFin : (n : Nat) -> Gen0 $ Fin n
genFin Z     = empty
genFin (S n) = elements $ forget $ allFins n

genAnyFin : Gen0 Nat => Gen0 (n ** Fin n)
genAnyFin @{genNat} = oneOf $ do
  n <- alternativesOf genNat
  f <- alternativesOf $ genFin n
  pure (n ** f)

Eq (n ** Fin n) where
  (n ** f) == (n' ** f') with (n `decEq` n')
    (n ** f) == (n ** f') | Yes Refl = f == f'
    _                     | No _     = False

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

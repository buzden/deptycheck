module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

genFin : (n : Nat) -> Gen $ Fin n
genFin Z     = empty
genFin (S n) = elements $ forget $ allFins n

mainFor : Nat -> IO ()
mainFor Z     = pure ()
mainFor n@(S k) = do
  let p = ratio 1 n
  printVerdict (genFin $ S k) $ fromList $
    [coverWith p (== f) | f <- forget $ allFins k]

main : IO ()
main = do
  mainFor 0
  mainFor 1
  mainFor 2
  mainFor 4
  mainFor 8
  mainFor 10
  mainFor 21

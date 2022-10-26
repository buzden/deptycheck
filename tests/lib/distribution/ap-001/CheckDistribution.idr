module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

nats : (n : Nat) -> List Nat
nats n = [0 .. n]

strs : (m : Nat) -> List String
strs m = [0 .. m] <&> \n => "s\{show n}"

bools : List Bool
bools = [False, True]

nats' = elements . nats
strs' = elements . strs
bools' = elements bools

record NSB where
  constructor MkNSB
  nf : Nat
  sf : String
  bf : Bool

g : Nat -> Nat -> Gen NSB
g n m = [| MkNSB (nats' n) (strs' m) bools' |]

mainFor : Nat -> Nat -> IO ()
mainFor n m = do
  -- Singles
  printVerdict (g n m) $ fromList $
    [ coverWith (ratio 1 $ S n) ((== n') . nf) | n' <- nats n ]
  printVerdict (g n m) $ fromList $
    [ coverWith (ratio 1 $ S m) ((== m') . sf) | m' <- strs m ]
  printVerdict (g n m) $ fromList $
    [ coverWith (ratio 1 2) ((== b') . bf) | b' <- bools ]
  -- Pairs
  printVerdict (g n m) $ fromList $
    [ coverWith (ratio 1 (S n) * ratio 1 (S m)) (\nsb => nsb.nf == n' && nsb.sf == m') | n' <- nats n, m' <- strs m ]
  printVerdict (g n m) $ fromList $
    [ coverWith (ratio 1 (S n) * ratio 1 2) (\nsb => nsb.nf == n' && nsb.bf == b') | n' <- nats n, b' <- bools ]
  printVerdict (g n m) $ fromList $
    [ coverWith (ratio 1 (S m) * ratio 1 2) (\nsb => nsb.sf == m' && nsb.bf == b') | m' <- strs m, b' <- bools ]
  -- Triples
  printVerdict (g n m) $ fromList $
    [ coverWith (ratio 1 (S n) * ratio 1 (S m) * ratio 1 2) (\nsb => nsb.nf == n' && nsb.sf == m' && nsb.bf == b') | n' <- nats n, m' <- strs m, b' <- bools ]

main : IO ()
main = do
  mainFor 0 0
  mainFor 0 2
  mainFor 4 7

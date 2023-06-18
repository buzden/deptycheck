module CheckDistribution

import Data.Maybe

import DistrCheckCommon

%default total

nats : Gen MaybeEmpty Nat
nats = elements [0 .. 9]

lists : (maxLen : Nat) -> Gen MaybeEmpty a -> Gen MaybeEmpty $ List a
lists Z     _  = pure []
lists (S n) as = oneOf
  [ [| [] |]
  , [| as :: lists n as |]
  ]

mainFor : (maxLen : Nat) -> IO ()
mainFor maxLen = printVerdict (lists maxLen nats) $ take (S maxLen) [0, 1 ..] <&> \l => do
                   let p = 1 / pow2 (fromNat $ if l == maxLen then l else S l)
                   coverWith p ((== l) . length)

main : IO ()
main = do
  mainFor 0
  mainFor 1
  mainFor 2
  mainFor 5

module CheckDistribution

import Data.Maybe

import DistrCheckCommon

%default total

nats : Gen0 Nat
nats = elements' [0 .. 9]

lists : (maxLen : Nat) -> Gen0 a -> Gen0 $ List a
lists Z     _  = pure []
lists (S n) as = frequency
  [ (1, [| [] |])
  , (3, [| as :: lists n as |])
  ]

forth : Probability
forth = 1/4

thf : Probability
thf = 3/4

thfN : Nat -> Probability
thfN 0 = 1
thfN 1 = thf
thfN (S n) = thf * thfN n

mainFor : (maxLen : Nat) -> IO ()
mainFor maxLen = printVerdict (lists maxLen nats) $ take maxLen [0, 1 ..] <&> \l => do
                   let p = thfN l * forth
                   coverWith p ((== l) . length)

main : IO ()
main = do
  mainFor 0
  mainFor 1
  mainFor 2
  mainFor 5
  mainFor 10

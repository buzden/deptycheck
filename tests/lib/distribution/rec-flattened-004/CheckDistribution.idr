module CheckDistribution

import Data.Maybe

import DistrCheckCommon

%default total

nats : Gen MaybeEmpty Nat
nats = elements [0 .. 100]

lists : (maxLen : Nat) -> Gen MaybeEmpty a -> Gen MaybeEmpty $ List a
lists Z     _  = pure []
lists (S n) as = oneOf
  $  [| [] |]
  :: [| [forgetAlternatives as] :: alternativesOf (lists n as) |]

mainFor : (maxLen : Nat) -> IO ()
mainFor maxLen = printVerdict (lists maxLen nats) $ take (S maxLen) [0, 1 ..] <&> \l => coverWith (ratio 1 (S maxLen)) ((== l) . length)

main : IO ()
main = do
  mainFor 0
  mainFor 1
  mainFor 2
  mainFor 10
  mainFor 20

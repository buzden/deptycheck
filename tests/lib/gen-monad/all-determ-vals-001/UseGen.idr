module UseGen

import Data.List.Lazy
import Test.DepTyCheck.Gen

%default total

gen : Gen MaybeEmpty (Nat, Nat)
gen = do
  a <- elements [1 .. 100]
  b <- elements [1 .. 100]
  if a == b then pure () else empty
  pure (a, b)

main : IO Unit
main = Lazy.traverse_ ((>> putStrLn "\n----\n") . printLn) $ allDetermValues gen

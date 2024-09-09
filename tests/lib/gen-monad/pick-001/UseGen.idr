module UseGen

import Test.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

gen : Gen MaybeEmpty (Nat, Nat)
gen = do
  a <- elements [1 .. 100]
  b <- elements [1 .. 100]
  if a == b then pure () else empty
  pure (a, b)

main : IO Unit
main = printLn . map (\(a, b) => a == b) =<< pick gen

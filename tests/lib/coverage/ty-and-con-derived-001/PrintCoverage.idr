module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%language ElabReflection

export %hint
smallStrs : Fuel -> Gen MaybeEmpty String
smallStrs _ = elements ["", "a", "bc"]

data X = X1 | X2 Nat | X3 String

data Y = Y1 | Y2 X | Y3 X X

genY : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty Y
genY = deriveGen

main : IO ()
main = do
  let ci = initCoverageInfo genY
  let vs = unGenTryND 100 someStdGen $ genY $ limit 10
  let mc = concatMap fst vs
  let ci = registerCoverage mc ci
  putStrLn $ show ci

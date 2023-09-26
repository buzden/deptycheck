module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%language ElabReflection

data X : Bool -> Type where
  X1 : X False
  X2 : (a : Maybe ()) -> X (isJust a)

genX : Gen MaybeEmpty (X False)
genX = do
  withCoverage (pure $ X1)

main : IO ()
main = do
  let ci = initCoverageInfo genX
  let vs = unGenTryND 100 someStdGen genX
  let mc = concatMap fst vs
  let ci = registerCoverage mc ci
  putStrLn $ show ci

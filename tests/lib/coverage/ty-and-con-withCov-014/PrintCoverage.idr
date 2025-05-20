module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%language ElabReflection

data Y : Fin n -> Type where
  Y1 : Y n
  Y2 : Y n

genY : Fuel -> {n : _} -> (f : Fin n) -> Gen NonEmpty $ Y f
genY fl _ = withCoverage $ oneOf [ pure Y1, pure Y2 ]

main : IO ()
main = do
  let ci = initCoverageInfo genY
  let vs = unGenTryND 100 someStdGen $ genY (limit 10) {n=15} 9
  let mc = concatMap fst vs
  let ci = registerCoverage mc ci
  putStrLn $ show ci

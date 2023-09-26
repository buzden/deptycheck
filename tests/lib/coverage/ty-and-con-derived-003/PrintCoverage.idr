module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%language ElabReflection

export %hint
UsedConstructorDerivator : ConstructorDerivator
UsedConstructorDerivator = LeastEffort

data X : Bool -> Type where
  XT : X True
  XF : X False

data Y : Type where
  YT : X True -> Y
  YF : X False -> Y

genX : Fuel -> (b : Bool) -> Gen MaybeEmpty $ X b
genX _ True  = empty
genX _ False = withCoverage $ pure XF

genY : Fuel -> (Fuel -> (b : Bool) -> Gen MaybeEmpty $ X b) => Gen MaybeEmpty Y
genY = deriveGen
-- since `XT` is not generated, `YT` should be not covered

main : IO ()
main = do
  let ci = initCoverageInfo genY
  let vs = unGenTryND 100 someStdGen $ genY @{genX} $ limit 10
  putStrLn $ "Number of successfully generated samples: \{show $ length $ toList vs}\n"
  let mc = concatMap fst vs
  let ci = registerCoverage mc ci
  putStrLn $ show ci

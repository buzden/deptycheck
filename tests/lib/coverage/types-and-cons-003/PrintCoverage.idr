module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%language ElabReflection

export
smallStrs : Fuel -> Gen NonEmpty String
smallStrs _ = elements ["", "a", "bc"]

data X = X1 | X2 Nat | X3 String

genX : Fuel -> Gen NonEmpty X
genX fl = oneOf
  [ pure X1
  , X3 <$> smallStrs fl
  ]

data Y = Y1 | Y2 X | Y3 X X

genY : Fuel -> Gen NonEmpty Y
genY fl = withCoverage $ oneOf
  [ [| Y1 |]
  , [| Y3 (genX fl) (genX fl) |]
  ]

main : IO ()
main = do
  let ci = initCoverageInfo genY
  let vs = unGenTryND 100 someStdGen $ genY $ limit 10
  let mc = concatMap fst vs
  let ci = registerCoverage mc ci
  putStrLn $ show ci

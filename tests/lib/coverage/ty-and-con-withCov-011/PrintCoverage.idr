module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen

import Control.Monad.Random
import System.Random.Pure.StdGen

%default total

%language ElabReflection

export
smallStrs : Fuel -> Gen NonEmpty String
smallStrs _ = elements ["", "a", "bc"]

data X = X1 | X2 Nat | X3 String

genX : Fuel -> Gen NonEmpty X
genX fl = withCoverage $ oneOf
  [ pure X1
  , X3 <$> smallStrs fl
  ]

data Y : Nat -> Type where
  Y1 : Y 0
  Y2 : X -> Y 1
  Y3 : X -> X -> Y n

genY : Fuel -> (n : _) -> Gen NonEmpty $ Y n
genY fl Z = withCoverage $ oneOf
  [ [| Y1 |]
  , [| Y3 (genX fl) (genX fl) |]
  ]
genY fl 1 = withCoverage [| Y2 (genX fl) |]
genY fl n = withCoverage [| Y3 (genX fl) (genX fl) |]

try : (CoverageGenInfo g) -> (n : Nat) -> IO ()
try ci n = do
  (Right v) <- runEitherT {e = ()} {m = IO} $ evalRandomT someStdGen $ unGenD $ genY (limit 5) n
    | Left err => putStrLn "Impossible!"
  let mc = fst v
  let ci = registerCoverage mc ci
  putStrLn $ show ci


main : IO ()
main = do
  let ci = initCoverageInfo genY
  try ci 0
  putStrLn "--------\n"
  try ci 1
  putStrLn "--------\n"
  try ci 3


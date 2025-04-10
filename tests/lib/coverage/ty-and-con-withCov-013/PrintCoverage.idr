module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen
import Deriving.Show

import Control.Monad.Maybe
import Control.Monad.Random
import System.Random.Pure.StdGen

%default total

%language ElabReflection

data X = X2 Nat | X3 String

genX : Fuel -> Gen MaybeEmpty X
genX fl = withCoverage $ oneOf
  [ [| X2 $ elements [0 .. 9] |]
  , [| X3 $ elements ["", "a", "bc"] |]
  ]

data Y : Nat -> Type where
  Y1 : Y 0
  Y2 : X -> Y 1
  Y3 : X -> X -> Y n

genY : Fuel -> (n : _) -> Gen MaybeEmpty $ Y n
genY fl n = withCoverage $ oneOf [ [| Y3 (genX fl) (genX fl) |], add n ] where
  add : (n : _) -> Gen MaybeEmpty $ Y n
  add 0 = [| Y1 |]
  add 1 = [| Y2 $ genX fl |]
  add _ = empty

%hint ShowX : Show X; ShowX = %runElab derive
%hint ShowY : Show (Y n); ShowY = %runElab derive

try : (n : Nat) -> IO ()
try n = do
  v : Maybe (Y n) <- evalRandomT someStdGen $ evalStateT Z $ unGen' {labels = PrintAllLabels} $ genY (limit 5) n
  let Just v = v
    | Nothing => putStrLn "couldn't produce a value"
  putStrLn "value: \{show v}"

main : IO ()
main = do
  Lazy.for_ [Z, 1, 3] $ \n => do
    putStrLn "--------\n"
    try n

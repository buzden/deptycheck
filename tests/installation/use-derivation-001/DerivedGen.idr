module DerivedGen

import Data.Fuel

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%language ElabReflection

%hint
UsedConstructorDerivator : ConstructorDerivator
UsedConstructorDerivator = LeastEffort

checkedGen : Fuel -> Gen Unit
checkedGen = deriveGen

main : IO Unit
main = do
  putStrLn "Generated values:"
  let genedValues = map show $ unGenTryN 10 someStdGen $ checkedGen $ limit 20
  Lazy.for_ genedValues $ (putStrLn "-----" >>) . putStrLn

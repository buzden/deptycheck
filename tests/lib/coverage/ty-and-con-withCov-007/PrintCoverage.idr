module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%language ElabReflection

%hide Language.Reflection.Syntax.var

data X : (post : List ()) -> Type where
  XZ : X post
  XS : X post -> X (var::post)

data Y : Type where
  MkY : (all : List ()) -> X all -> Y

genY : Nat -> Gen MaybeEmpty Y
genY 0 = pure $ MkY [] XZ
genY (S k) = do
  MkY a b <- genY k
  withCoverage (pure $ XS b) <&> MkY (()::a)

main : IO ()
main = do
  let ci = initCoverageInfo genY
  do let vs = unGenTryND 100 someStdGen $ genY 0
     let mc = concatMap fst vs
     let ci = registerCoverage mc ci
     putStrLn $ show ci
  putStrLn "\n--------\n"
  do let vs = unGenTryND 100 someStdGen $ genY 3
     let mc = concatMap fst vs
     let ci = registerCoverage mc ci
     putStrLn $ show ci

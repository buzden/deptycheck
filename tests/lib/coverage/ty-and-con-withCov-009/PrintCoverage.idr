module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%language ElabReflection

data X : (n : Nat) -> Fin n -> Type where
  X1 : X 1 FZ
  X2 : (n : Nat) -> IsSucc n => X n (case n of S _ => FZ)

genX' : (n : Nat) -> Gen MaybeEmpty (f ** X n f)
genX' 0       = empty
genX' 1       = oneOf [ pure (_ ** X1), pure (FZ ** X2 1) ]
genX' n@(S _) = pure (FZ ** X2 n)

genX : (n : Nat) -> Gen MaybeEmpty (f ** X n f)
genX n = withCoverage $ genX' n

main : IO ()
main = do
  let ci = initCoverageInfo genX
  do let vs = unGenTryND 100 someStdGen $ genX 0
     let mc = concatMap fst vs
     let ci = registerCoverage mc ci
     putStrLn $ show ci
  putStrLn "\n--------\n"
  do let vs = unGenTryND 100 someStdGen $ genX 1
     let mc = concatMap fst vs
     let ci = registerCoverage mc ci
     putStrLn $ show ci
  putStrLn "\n--------\n"
  do let vs = unGenTryND 100 someStdGen $ genX 2
     let mc = concatMap fst vs
     let ci = registerCoverage mc ci
     putStrLn $ show ci

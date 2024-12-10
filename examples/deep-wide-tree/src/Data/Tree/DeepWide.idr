module Data.Tree.DeepWide

import public Test.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

public export
data DW : Nat -> Type where
  B : (a, b, c, d, e, f : Nat) -> DW Z
  R : (a, b, c, d, e, f : DW n) -> DW (S n)

n : Gen1 Nat
n = elements $ 1 :: [ 2 .. 99 ]

-- Gen for DW based on `<*>`
export
a : {n : Nat} -> Gen1 (DW n)
a {n=Z}   = [| B n n n n n n |]
a {n=S _} = [| R a a a a a a |]

-- Gen for DW based on `>>=`
export
b : {n : Nat} -> Gen1 (DW n)
b {n=Z}   = pure $ B !n !n !n !n !n !n
b {n=S _} = pure $ R !b !b !b !b !b !b

export
runN : (cnt, depth : Nat) -> Gen1 (DW depth) -> IO ()
runN cnt _ = printLn . length . take cnt . unGenAll someStdGen

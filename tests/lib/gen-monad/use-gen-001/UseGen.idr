module UseGen

import Data.Fin
import Data.List.Lazy

import Test.DepTyCheck.Gen

import System.File
import System.Random.Pure.StdGen

fin_uni_gen : {rc : Nat} -> Gen MaybeEmpty (Fin rc)
fin_uni_gen {rc=Z}   = empty
fin_uni_gen {rc=S _} = chooseAny

runOnce : (variant : Nat) -> Gen MaybeEmpty a -> LazyList a
runOnce v = unGenTryN 100 someStdGen . variant v

for' : Monad f => LazyList a -> (a -> f Unit) -> f Unit
for' xs g = foldrLazy ((>>) . g) (pure ()) xs

printOnce : Show a => (n : Nat) -> Gen MaybeEmpty a -> IO Unit
printOnce n gen = for' (iterateN n S Z) $ \v => do
  print "\n---------\n"
  let (x::_) = runOnce v gen
    | [] => print "none"
  print $ show x
  where
    print : String -> IO Unit
    print s = putStrLn s >> fflush stdout

main : IO Unit
main = printOnce 5 $ fin_uni_gen {rc=6}

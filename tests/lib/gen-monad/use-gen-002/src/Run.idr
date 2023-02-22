module Run

import Control.Monad.State

import Data.Fuel
import Data.List.Lazy

import GenForSome

import Test.DepTyCheck.Gen

import System.File.Process
import System.File.Virtual

import System.Random.Pure.StdGen

Show (Stmts preDefs postDefs) where
  show $ Def new = "define `\{new}`"
  show $ Use usd = "use `\{usd}`"
  show $ x >> y  = show x ++ "\n" ++ show y

namespace NoParams

  export
  ShowStmts : Show $ Stmts preDefs postDefs
  ShowStmts = %search

namespace PreOnly

  export
  [ShowStmt] Show (preDefs ** Stmts preDefs postDefs) where
    show (preDefs ** stmt) = "-- pre defs: \{show preDefs}\n\{show stmt}"

namespace PostOnly

  export
  [ShowStmt] Show (postDefs ** Stmts preDefs postDefs) where
    show (postDefs ** stmt) = "\{show stmt}\n-- post defs: \{show postDefs}"

namespace BothPreAndPost

  export
  [ShowStmt] Show (preDefs ** postDefs ** Stmts preDefs postDefs) where
    show (preDefs ** postDefs ** stmt) = "-- pre defs: \{show preDefs}\n\{show stmt}\n-- post defs: \{show postDefs}"

runOnce : (variant : Nat) -> Gen a -> LazyList a
runOnce v = unGenTryN 100 someStdGen . variant v

for' : Monad f => LazyList a -> (a -> f Unit) -> f Unit
for' xs g = foldrLazy ((>>) . g) (pure ()) xs

printOnce : Show a => (n : Nat) -> Gen a -> IO Unit
printOnce n gen = for' (iterateN n S Z) $ \v => do
  print "\n---------\n"
  let (x::_) = runOnce v gen
    | [] => print "none"
  print $ show x
  where
    print : String -> IO Unit
    print s = putStrLn s >> fflush stdout

main : IO Unit
main = printOnce @{ShowStmt} 5 $ genStmtP_ (limit 1) []

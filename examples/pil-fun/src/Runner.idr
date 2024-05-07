module Runner

import Data.Fuel
import Data.List.Lazy

import Language.PilFun.Gen
import Language.PilFun.Pretty.DSL
import Language.PilFun.Pretty.Gen

import Test.DepTyCheck.Gen

import Text.PrettyPrint.Bernardy

import System.Random.Pure.StdGen

%default total

stdFuns : NamedCtxt
stdFuns = do
  AddFun True  "+"  $ [< Int', Int'] ==> Just Int'
  AddFun True  "<"  $ [< Int', Int'] ==> Just Bool'
  AddFun True  "<=" $ [< Int', Int'] ==> Just Bool'
  AddFun True  "==" $ [< Int', Int'] ==> Just Bool'
  AddFun True  "||" $ [< Bool', Bool'] ==> Just Bool'
  AddFun True  "&&" $ [< Bool', Bool'] ==> Just Bool'
  AddFun False "!"  $ [< Bool'] ==> Just Bool'
  AddFun False "Console.println" $ [< Int'] ==> Nothing
  Enough

prettyOpts : LayoutOpts
prettyOpts = Opts 152

namesGen : Gen0 String
namesGen = pack <$> listOf {length = choose (1,10)} (choose ('a', 'z'))

export
main : IO ()
main = do
  let modelFuel = limit 8
  let ppFuel = limit 1000000
  let vals = unGenTryN 10 someStdGen $
               genStmts modelFuel stdFuns.functions stdFuns.variables Nothing >>= printScala3 @{stdFuns.fvNames} @{namesGen} ppFuel
  Lazy.for_ vals $ \val => do
    putStrLn "///////////////////\n"
    putStr $ render prettyOpts val

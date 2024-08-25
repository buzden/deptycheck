module Runner

import Data.Fuel
import Data.List.Lazy
import Data.List1
import Data.SortedMap
import Data.String

import Language.PilFun.Derived
import Language.PilFun.Pretty.Derived
import Language.PilFun.Pretty.DSL
import Language.PilFun.Pretty.Scala3

import Test.DepTyCheck.Gen

import Text.PrettyPrint.Bernardy

import System
import System.GetOpts
import System.Random.Pure.StdGen

%default total

-------------------
--- CLI options ---
-------------------

record Config where
  constructor MkConfig
  usedSeed : IO StdGen
  layoutOpts : LayoutOpts
  testsCnt   : Nat
  modelFuel  : Fuel
  ppFuel     : Fuel

defaultConfig : Config
defaultConfig = MkConfig
  { usedSeed = initSeed
  , layoutOpts = Opts 152
  , testsCnt   = 10
  , modelFuel  = limit 8
  , ppFuel     = limit 1000000
  }

parseSeed : String -> Either String $ Config -> Config
parseSeed str = do
  let n1:::n2::[] = trim <$> split (== ',') str
    | _ => Left "we expect two numbers divided by a comma"
  let Just n1 = parsePositive n1
    | Nothing => Left "expected a positive number at the first component, given `\{n1}`"
  let Just n2 = parsePositive {a=Bits64} n2
    | Nothing => Left "expected a positive number at the second component, given `\{n2}`"
  let Yes prf = decSo $ testBit n2 0
    | No _ => Left "second component must be odd"
  Right {usedSeed := pure $ rawStdGen n1 n2}

parsePPWidth : String -> Either String $ Config -> Config
parsePPWidth str = case parsePositive str of
  Just n  => Right {layoutOpts := Opts n}
  Nothing => Left "can't parse max width for the pretty-printer"

parseTestsCount : String -> Either String $ Config -> Config
parseTestsCount str = case parsePositive str of
  Just n  => Right {testsCnt := n}
  Nothing => Left "can't parse given count of tests"

parseModelFuel : String -> Either String $ Config -> Config
parseModelFuel str = case parsePositive str of
  Just n  => Right {modelFuel := limit n}
  Nothing => Left "can't parse given model fuel"

parsePPFuel : String -> Either String $ Config -> Config
parsePPFuel str = case parsePositive str of
  Just n  => Right {ppFuel := limit n}
  Nothing => Left "can't parse given pretty-printer fuel"

cliOpts : List $ OptDescr $ Config -> Config
cliOpts =
  [ MkOpt [] ["seed"]
      (ReqArg' parseSeed "<seed>,<gamma>")
      "Sets particular random seed to start with."
  , MkOpt ['w'] ["pp-width"]
      (ReqArg' parsePPWidth "<nat>")
      "Sets the max length for the pretty-printer."
  , MkOpt ['n'] ["tests-count"]
      (ReqArg' parseTestsCount "<tests-count>")
      "Sets the count of tests to generate."
  , MkOpt [] ["model-fuel"]
      (ReqArg' parseModelFuel "<fuel>")
      "Sets how much fuel there is for generation of the model."
  , MkOpt [] ["pp-fuel"]
      (ReqArg' parsePPFuel "<fuel>")
      "Sets how much fuel there is for pretty-printing."
  ]

---------------
--- Running ---
---------------

namesGen : Gen0 String
namesGen = pack <$> listOf {length = choose (1,10)} (choose ('a', 'z'))

run : Config ->
      NamedCtxt ->
      (pp : PP) ->
      IO ()
run conf ctxt pp = do
  seed <- conf.usedSeed
  let vals = unGenTryN conf.testsCnt seed $
               genStmts conf.modelFuel ctxt.functions ctxt.variables Nothing >>=
                 pp @{ctxt.fvNames} @{namesGen} conf.ppFuel
  Lazy.for_ vals $ \val => do
    putStrLn "-------------------\n"
    putStr $ render conf.layoutOpts val

-----------------------
--- Language config ---
-----------------------

scala3StdFuns : NamedCtxt
scala3StdFuns = do
  AddFun True  "+"  $ [< Int', Int'] ==> Just Int'
  AddFun True  "<"  $ [< Int', Int'] ==> Just Bool'
  AddFun True  "<=" $ [< Int', Int'] ==> Just Bool'
  AddFun True  "==" $ [< Int', Int'] ==> Just Bool'
  AddFun True  "||" $ [< Bool', Bool'] ==> Just Bool'
  AddFun True  "&&" $ [< Bool', Bool'] ==> Just Bool'
  AddFun False "!"  $ [< Bool'] ==> Just Bool'
  AddFun False "Console.println" $ [< Int'] ==> Nothing
  Enough

supportedLanguages : SortedMap String (NamedCtxt, PP)
supportedLanguages = fromList
  [ ("scala3", scala3StdFuns, printScala3)
  ]

---------------
--- Startup ---
---------------

export
main : IO ()
main = do
  args <- getArgs
  let usage : Lazy String := usageInfo "Usage: \{fromMaybe "pil-fun" $ head' args} [options] <language>" cliOpts
  let langs : Lazy String := joinBy ", " $ SortedSet.toList $ keySet supportedLanguages
  let MkResult options nonOptions [] [] = getOpt Permute cliOpts $ drop 1 args
    | MkResult {unrecognized=unrecOpts@(_::_), _} => if "help" `elem` unrecOpts
                                                       then putStrLn usage
                                                       else die "unrecodnised options \{show unrecOpts}\n\{usage}"
    | MkResult {errors=es@(_::_), _}              => die "arguments parse errors \{show es}\n\{usage}"
  let [lang] = nonOptions
    | []   => die "no language is given, supported languages: \{langs}\n\{usage}"
    | many => die "too many languages are given\n\{usage}"
  let Just (ctxt, pp) = lookup lang supportedLanguages
    | Nothing => die "unknown language \{lang}, supported languages \{langs}\n\{usage}"

  let config = foldl (flip apply) defaultConfig options

  run config ctxt pp

module Language.PilFun.Pretty

import Data.Fuel
import Data.SnocList
import Data.So

import Deriving.DepTyCheck.Util.Alternative

import public Language.PilFun

import Test.DepTyCheck.Gen

import public Text.PrettyPrint.Bernardy

import System.Random.Pure.StdGen

%default total

data UniqNames : Nat -> Type
data NameIsNew : (n : Nat) -> UniqNames n -> String -> Type

data UniqNames : Nat -> Type where
  Nil  : UniqNames Z
  (::) : (s : String) -> (ss : UniqNames n) -> (0 _ : NameIsNew n ss s) => UniqNames (S n)

data NameIsNew : (n : Nat) -> UniqNames n -> String -> Type where
  N : NameIsNew Z [] x
  S : (0 _ : So $ x /= s) => NameIsNew n ss x -> NameIsNew (S n) ((s::ss) @{sub}) x

genNewName : Fuel -> (Fuel -> Gen MaybeEmpty String) => (n : Nat) -> (ss : UniqNames n) -> Gen MaybeEmpty $ DPair String $ NameIsNew n ss

-- When both functions and variables namespaces are shared
Names : (funs : SnocListFunSig) -> (vars : SnocListTy) -> Type
Names funs vars = UniqNames $ funs.length + vars.length

varName : {funs : _} -> {vars : _} -> Names funs vars => IndexIn vars -> String
varName {funs=funs:<_} @{_::_}  i         = varName {funs} i
varName {funs=[<]}     @{n::ns} Here      = n
varName {funs=[<]}     @{n::ns} (There i) = varName {funs=[<]} i

withNewVar : {a : _} -> (names : UniqNames (a + b)) => (s : String) -> NameIsNew (a + b) names s => UniqNames (a + S b)

funName : {funs : SnocListFunSig} -> Names funs vars => IndexIn funs -> String
funName @{n::ns} Here      = n
funName @{n::ns} (There i) = funName @{ns} i

toList : UniqNames n -> List String
toList [] = []
toList (s::ss) = s :: toList ss

isNop : Stmts funs vars mfd retTy -> Bool
isNop Nop = True
isNop _   = False

namespace Scala3

  printTy : Ty -> Doc opts
  printTy Int'  = "Int"
  printTy Bool' = "Boolean"

  printExpr : {funs : _} -> {vars : _} -> {opts : _} ->
              (names : Names funs vars) =>
              Prec -> Expr funs vars ty -> Doc opts
  printExprs : {funs : _} -> {vars : _} -> {opts : _} ->
               (names : Names funs vars) =>
               ExprsSnocList funs vars argTys -> SnocList $ Doc opts
  printFunCall : {funs : _} -> {vars : _} -> {opts : _} ->
                 (names : Names funs vars) =>
                 IndexIn funs -> ExprsSnocList funs vars argTys -> Doc opts
  printFunCall n args = do
    let lhs = line $ funName {vars} n
    let args = tuple (toList $ printExprs args)
    ifMultiline (lhs <+> args) (flush lhs <+> indent 2 args)
  -- TODO to support infix operations

  printExpr p $ C $ I k     = line $ show k
  printExpr p $ C $ B False = "false"
  printExpr p $ C $ B True  = "true"
  printExpr p $ V n         = line $ varName {funs} n
  printExpr p $ F n args    = printFunCall n args

  printExprs [<] = [<]
  printExprs (sx:<x) = printExprs sx :< printExpr Open x

  export
  printScala3 : {funs : _} -> {vars : _} -> {mfd : _} -> {retTy : _} -> {opts : _} ->
                (names : Names funs vars) =>
                (newNames : Gen0 String) =>
                Fuel ->
                Stmts funs vars mfd retTy -> Gen0 $ Doc opts

  printSubScala3 : {funs : _} -> {vars : _} -> {mfd : _} -> {retTy : _} -> {opts : _} ->
                   (names : Names funs vars) =>
                   (newNames : Gen0 String) =>
                   Fuel ->
                   Stmts funs vars mfd retTy -> Gen0 $ Doc opts
  printSubScala3 _  Nop = pure "{}"
  printSubScala3 fl ss  = printScala3 fl ss

  printScala3 fl $ NewV ty initial cont = do
    (nm ** _) <- genNewName fl _ names
    rest <- printScala3 @{withNewVar nm} fl cont
    let tyAscr = if !chooseAny then ":" <++> printTy ty else empty
    pure $ flip vappend rest $ do
      let lhs = "var" <++> line nm <++> tyAscr <++> "="
      let rhs = printExpr Open initial
      ifMultiline (lhs <++> rhs) (flush lhs <+> indent 2 rhs)

  printScala3 fl $ NewF sig body cont = do
    (nm ** _) <- genNewName fl _ names
    rest <- printScala3 @{nm::names} fl cont
    body <- printSubScala3 @{?subnames} fl body
    ?printScala3_rhs_1

  printScala3 fl $ (#=) n v cont = (line (varName {funs} n) <++> "=" <++> printExpr Open v `vappend`) <$> printScala3 fl cont

  printScala3 fl $ If cond th el cont = do
    rest <- printScala3 fl cont
    pure $ flip vappend rest $ vsep $
      [ "if" <++> printExpr Open cond <++> "then"
      , indent 2 !(printSubScala3 fl th)
      ] ++ whenTs (not (isNop el) || !chooseAny)
      [ "else"
      , indent 2 !(printSubScala3 fl el)
      ]

  printScala3 fl $ Call n args cont = (printFunCall n args `vappend`) <$> printScala3 fl cont

  printScala3 fl $ Ret x = pure $ "return" <++> printExpr Open x

  printScala3 fl $ Nop = pure ""

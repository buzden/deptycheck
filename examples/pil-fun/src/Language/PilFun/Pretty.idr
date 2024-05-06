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

data UniqNames : Funs -> Vars -> Type
data NameIsNew : (funs : Funs) -> (vars : Vars) -> UniqNames funs vars -> String -> Type

data UniqNames : Funs -> Vars -> Type where
  Empty  : UniqNames [<] [<]
  NewFun : (ss : UniqNames funs vars) => (s : String) -> (0 _ : NameIsNew funs vars ss s) => UniqNames (funs:<fun) vars
  NewVar : (ss : UniqNames funs vars) => (s : String) -> (0 _ : NameIsNew funs vars ss s) => UniqNames funs (vars:<var)

data NameIsNew : (funs : Funs) -> (vars : Vars) -> UniqNames funs vars -> String -> Type where
  E : NameIsNew [<] [<] Empty x
  F : (0 _ : So $ x /= s) => NameIsNew funs vars ss x -> NameIsNew (funs:<fun) vars (NewFun @{ss} x @{sub}) x
  V : (0 _ : So $ x /= s) => NameIsNew funs vars ss x -> NameIsNew funs (vars:<var) (NewVar @{ss} x @{sub}) x

genNewName : Fuel -> (Fuel -> Gen MaybeEmpty String) =>
             (funs : Funs) -> (vars : Vars) -> (names : UniqNames funs vars) ->
             Gen MaybeEmpty $ DPair String $ NameIsNew funs vars names

varName : UniqNames funs vars => IndexIn vars -> String
varName @{(NewFun @{ss} s)} i         = varName @{ss} i
varName @{(NewVar @{ss} s)} Here      = s
varName @{(NewVar @{ss} s)} (There i) = varName @{ss} i

funName : UniqNames funs vars => IndexIn funs -> String
funName @{(NewFun @{ss} s)} Here      = s
funName @{(NewFun @{ss} s)} (There i) = funName @{ss} i
funName @{(NewVar @{ss} s)} i         = funName @{ss} i

isNop : Stmts funs vars mfd retTy -> Bool
isNop Nop = True
isNop _   = False

namespace Scala3

  printTy : Ty -> Doc opts
  printTy Int'  = "Int"
  printTy Bool' = "Boolean"

  printExpr : {funs : _} -> {vars : _} -> {opts : _} ->
              (names : UniqNames funs vars) =>
              Prec -> Expr funs vars ty -> Doc opts
  printExprs : {funs : _} -> {vars : _} -> {opts : _} ->
               (names : UniqNames funs vars) =>
               ExprsSnocList funs vars argTys -> SnocList $ Doc opts
  printFunCall : {funs : _} -> {vars : _} -> {opts : _} ->
                 (names : UniqNames funs vars) =>
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
                (names : UniqNames funs vars) =>
                (newNames : Gen0 String) =>
                Fuel ->
                Stmts funs vars mfd retTy -> Gen0 $ Doc opts

  printSubScala3 : {funs : _} -> {vars : _} -> {mfd : _} -> {retTy : _} -> {opts : _} ->
                   (names : UniqNames funs vars) =>
                   (newNames : Gen0 String) =>
                   Fuel ->
                   Stmts funs vars mfd retTy -> Gen0 $ Doc opts
  printSubScala3 _  Nop = pure "{}"
  printSubScala3 fl ss  = printScala3 fl ss

  printScala3 fl $ NewV ty initial cont = do
    (nm ** _) <- genNewName fl _ _ names
    rest <- printScala3 @{NewVar nm} fl cont
    let tyAscr = if !chooseAny then ":" <++> printTy ty else empty
    pure $ flip vappend rest $ do
      let lhs = "var" <++> line nm <++> tyAscr <++> "="
      let rhs = printExpr Open initial
      ifMultiline (lhs <++> rhs) (flush lhs <+> indent 2 rhs)

  printScala3 fl $ NewF sig body cont = do
    (nm ** _) <- genNewName fl _ _ names
    rest <- printScala3 @{NewFun nm} fl cont
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

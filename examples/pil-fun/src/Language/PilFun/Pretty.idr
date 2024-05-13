module Language.PilFun.Pretty

import Data.Fuel
import Data.SnocList
import public Data.So
import Data.Vect

import Deriving.DepTyCheck.Util.Alternative

import public Language.PilFun

import Test.DepTyCheck.Gen

import public Text.PrettyPrint.Bernardy

import System.Random.Pure.StdGen

%default total

public export
data UniqNames : Funs -> Vars -> Type
public export
data NameIsNew : (funs : Funs) -> (vars : Vars) -> UniqNames funs vars -> String -> Type

data UniqNames : Funs -> Vars -> Type where
  Empty  : UniqNames [<] [<]
  NewFun : (ss : UniqNames funs vars) => (s : String) -> (0 _ : NameIsNew funs vars ss s) =>
           {default False isInfix : Bool} -> (0 infixCond : So $ not isInfix || fun.From.length >= 1) =>
           UniqNames (funs:<fun) vars
  NewVar : (ss : UniqNames funs vars) => (s : String) -> (0 _ : NameIsNew funs vars ss s) => UniqNames funs ((:<) vars var mut)

data NameIsNew : (funs : Funs) -> (vars : Vars) -> UniqNames funs vars -> String -> Type where
  E : NameIsNew [<] [<] Empty x
  F : (0 _ : So $ x /= s) -> NameIsNew funs vars ss x -> NameIsNew (funs:<fun) vars (NewFun @{ss} {isInfix} s @{sub} @{infixCond}) x
  V : (0 _ : So $ x /= s) -> NameIsNew funs vars ss x -> NameIsNew funs ((:<) vars var mut) (NewVar @{ss} s @{sub}) x

genNewName : Fuel -> (Fuel -> Gen MaybeEmpty String) =>
             (funs : Funs) -> (vars : Vars) -> (names : UniqNames funs vars) ->
             Gen MaybeEmpty (s ** NameIsNew funs vars names s)

varName : UniqNames funs vars => IndexIn vars -> String
varName @{(NewFun @{ss} _)} i         = varName @{ss} i
varName @{(NewVar       s)} Here      = s
varName @{(NewVar @{ss} _)} (There i) = varName @{ss} i

funName : UniqNames funs vars => IndexIn funs -> String
funName @{(NewFun       s)} Here      = s
funName @{(NewFun @{ss} _)} (There i) = funName @{ss} i
funName @{(NewVar @{ss} _)} i         = funName @{ss} i

isFunInfix : UniqNames funs vars => IndexIn funs -> Bool
isFunInfix @{(NewFun {isInfix} _)} Here  = isInfix
isFunInfix @{(NewFun @{ss} s)} (There i) = isFunInfix @{ss} i
isFunInfix @{(NewVar @{ss} s)} i         = isFunInfix @{ss} i

-- Returned vect has a reverse order; I'd like some `SnocVect` here.
newVars : (newNames : Gen0 String) =>
          {funs : _} -> {vars : _} ->
          Fuel ->
          (extraVars : _) -> UniqNames funs vars ->
          Gen0 (UniqNames funs (vars ++ extraVars), Vect extraVars.length (String, Ty))
newVars _  [<]     names = pure (names, [])
newVars fl (vs:<v) names = do
  (names', vts) <- newVars fl vs names
  (nm ** _) <- genNewName fl _ _ names'
  pure (NewVar @{names'} nm, (nm, v)::vts)

isNop : Stmts funs vars retTy -> Bool
isNop Nop = True
isNop _   = False

namespace Scala3

  printTy : Ty -> Doc opts
  printTy Int'  = "Int"
  printTy Bool' = "Boolean"

  printMaybeTy : MaybeTy -> Doc opts
  printMaybeTy Nothing   = "Unit"
  printMaybeTy $ Just ty = printTy ty

  getExprs : ExprsSnocList funs vars argTys -> SnocList $ Exists $ Expr funs vars
  getExprs [<] = [<]
  getExprs (sx:<x) = getExprs sx :< Evidence _ x

  printExpr : {funs : _} -> {vars : _} -> {opts : _} ->
              (names : UniqNames funs vars) =>
              Prec -> Expr funs vars ty -> Gen0 $ Doc opts
  printFunCall : {funs : _} -> {vars : _} -> {opts : _} ->
                 (names : UniqNames funs vars) =>
                 Prec ->
                 IndexIn funs -> ExprsSnocList funs vars argTys -> Gen0 $ Doc opts
  printFunCall p n args = do
    let f = line $ funName {vars} n
    let args = toList $ getExprs args
    let tupledArgs = \as => map tuple $ for as $ \(Evidence _ e) => printExpr Open e
    case (isFunInfix @{names} n, args) of
      -- Call for bitwise infix extension method
      (True, [Evidence _ l, Evidence _ r]) => pure $ parenthesise (p >= App) $ !(printExpr App l) <++> f <++> !(printExpr App r)
      -- Call for appropriate extension method with 0, 2 or more arguments
      (True, Evidence _ head :: args) => pure $ parenthesise (p >= App) $ !(printExpr App head) <+> "." <+> f <+> !(tupledArgs args)
      -- Call for normal function
      _ => pure $ ifMultiline (f <+> !(tupledArgs args)) (flush f <+> indent 2 !(tupledArgs args))

  printExpr p $ C $ I k     = pure $ line $ show k
  printExpr p $ C $ B False = pure $ "false"
  printExpr p $ C $ B True  = pure $ "true"
  printExpr p $ V n         = pure $ line $ varName {funs} n
  printExpr p $ F n args    = assert_total printFunCall p n args

  export
  printScala3 : {funs : _} -> {vars : _} -> {retTy : _} -> {opts : _} ->
                (names : UniqNames funs vars) =>
                (newNames : Gen0 String) =>
                Fuel ->
                Stmts funs vars retTy -> Gen0 $ Doc opts

  printSubScala3 : {funs : _} -> {vars : _} -> {retTy : _} -> {opts : _} ->
                   (names : UniqNames funs vars) =>
                   (newNames : Gen0 String) =>
                   Fuel ->
                   Stmts funs vars retTy -> Gen0 $ Doc opts
  printSubScala3 _  Nop = pure "{}"
  printSubScala3 fl ss  = printScala3 fl ss

  printScala3 fl $ NewV ty mut initial cont = do
    (nm ** _) <- genNewName fl _ _ names
    rest <- printScala3 @{NewVar nm} fl cont
    let tyAscr = if !chooseAny then ":" <++> printTy ty else empty
    let declPref = case mut of
                     Mutable   => "var"
                     Immutable => "val"
    let lhs = declPref <++> line nm <++> tyAscr <++> "="
    rhs <- printExpr Open initial
    pure $ flip vappend rest $ do
      ifMultiline (lhs <++> rhs) (flush lhs <+> indent 2 rhs)

  printScala3 fl $ NewF sig body cont = do
    (nm ** _) <- genNewName fl _ _ names
    isInfix <- chooseAny
    let (isInfix ** infixCond) : (b ** So (not b || sig.From.length >= 1)) = case decSo _ of
                                                                               Yes condMet => (isInfix ** condMet)
                                                                               No _        => (False ** Oh)
    rest <- printScala3 @{NewFun {isInfix} {infixCond} nm} fl cont
    (namesInside, funArgs) <- newVars fl _ names
    funBody <- printSubScala3 @{namesInside} fl body
    pure $ flip vappend rest $ do
      let funArgs = reverse (toList funArgs) <&> \(n, ty) => line n <+> ":" <++> printTy ty
      let defTail : List (Doc opts) -> Doc opts
          defTail funArgs = "def" <++> line nm <+> tuple funArgs <+> ":" <++> printMaybeTy sig.To <++> "="
      let (extPref, funSig) = case (isInfix, funArgs) of
                     (True, head::funArgs) => (Just $ "extension" <++> parens head, defTail funArgs)
                     _                     => (Nothing                            , defTail funArgs)
      let mainDef = ifMultiline (funSig <++> funBody) (flush funSig <+> indent 2 funBody)
      case extPref of
        Nothing      => mainDef
        Just extPref => ifMultiline (extPref <++> mainDef) (flush extPref <+> indent 2 mainDef)

  printScala3 fl $ (#=) n v cont = pure $ flip vappend !(printScala3 fl cont) $
    line (varName {funs} n) <++> "=" <++> !(printExpr Open v)

  printScala3 fl $ If cond th el cont = do
    rest <- printScala3 fl cont
    pure $ flip vappend rest $ vsep $
      [ "if" <++> !(printExpr Open cond) <++> "then"
      , indent 2 !(printSubScala3 fl th)
      ] ++ whenTs (not (isNop el) || !chooseAny)
      [ "else"
      , indent 2 !(printSubScala3 fl el)
      ]

  printScala3 fl $ Call n args cont = [| printFunCall Open n args `vappend` printScala3 fl cont |]

  printScala3 fl $ Ret x = ("return" <++>) <$> printExpr Open x

  printScala3 fl $ Nop = pure ""

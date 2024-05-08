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

isRet : Stmts funs vars retTy -> Bool
isRet $ Ret {} = True
isRet _        = False

getExprs : ExprsSnocList funs vars argTys -> SnocList $ Exists $ Expr funs vars
getExprs [<] = [<]
getExprs (sx:<x) = getExprs sx :< Evidence _ x

whenTs : Bool -> Doc opts -> Doc opts
whenTs b = if b then id else const empty

indentE : {opts : _} -> Nat -> Doc opts -> Doc opts
indentE n x = do
  l <- x
  pure $ if isEmpty l then l else indent n l

wrapBrIf : {opts : _} -> (indeed : Bool) -> Doc opts -> Doc opts -> Doc opts
wrapBrIf False pre x = pre `vappend` indentE 2 x
wrapBrIf True pre x = ifMultiline (pre <++> "{" <++> x <++> "}") (vsep [pre <++> "{", indentE 2 x, "}"])

namespace Scala3

  printTy : Ty -> Doc opts
  printTy Int'  = "Int"
  printTy Bool' = "Boolean"

  printMaybeTy : MaybeTy -> Doc opts
  printMaybeTy Nothing   = "Unit"
  printMaybeTy $ Just ty = printTy ty

  wrapMain : {opts : _} -> (indeed : Bool) -> Doc opts -> Doc opts
  wrapMain False x = x
  wrapMain True body = vsep
    [ ""
    , "@main"
    , "def main(): Unit = {"
    , indentE 2 body
    , "}"
    ]

  unaryOps : List String
  unaryOps = ["+", "-", "!", "~"]

  isUnaryOp : String -> List arg -> Bool
  isUnaryOp str xs = elem str unaryOps && length xs == 1

  printExpr : {funs : _} -> {vars : _} -> {opts : _} ->
              (names : UniqNames funs vars) =>
              Prec -> Expr funs vars ty -> Gen0 $ Doc opts
  printFunCall : {funs : _} -> {vars : _} -> {opts : _} ->
                 (names : UniqNames funs vars) =>
                 Prec ->
                 IndexIn funs -> ExprsSnocList funs vars argTys -> Gen0 $ Doc opts
  printFunCall p n args = do
    let fn = funName {vars} n
    let f = line fn
    let args = toList $ getExprs args
    let tupledArgs = \as => map tuple $ for as $ \(Evidence _ e) => printExpr Open e
    case (isFunInfix @{names} n, args, !(chooseAnyOf Bool)) of
      -- Call for bitwise infix extension method
      (True, [Evidence _ l, Evidence _ r], True) => pure $ parenthesise (p >= App) $ !(printExpr App l) <++> f <++> !(printExpr App r)
      -- Call for appropriate extension method with 0, 2 or more arguments
      (True, Evidence _ head :: args, _) => pure $ parenthesise (p >= App) $ !(printExpr App head) <+> "." <+> f <+> !(tupledArgs args)
      -- Call for normal function
      _ => pure $ parenthesise (p >= App && isUnaryOp fn args) $ hang' 2 f !(tupledArgs args)

  printExpr p $ C $ I k     = pure $ line $ show k
  printExpr p $ C $ B False = pure $ "false"
  printExpr p $ C $ B True  = pure $ "true"
  printExpr p $ V n         = pure $ line $ varName {funs} n
  printExpr p $ F n args    = assert_total printFunCall p n args

  printStmts : {funs : _} -> {vars : _} -> {retTy : _} -> {opts : _} ->
               (names : UniqNames funs vars) =>
               (newNames : Gen0 String) =>
               Fuel ->
               (toplevel : Bool) ->
               Stmts funs vars retTy -> Gen0 $ Doc opts

  printSubStmts : {funs : _} -> {vars : _} -> {retTy : _} -> {opts : _} ->
                  (names : UniqNames funs vars) =>
                  (newNames : Gen0 String) =>
                  Fuel ->
                  (noEmpty : Bool) ->
                  Stmts funs vars retTy -> Gen0 $ Doc opts
  printSubStmts _  True Nop = pure "{}"
  printSubStmts fl _    ss  = printStmts fl False ss

  printStmts fl tl $ NewV ty mut initial cont = do
    (nm ** _) <- genNewName fl _ _ names
    rest <- printStmts @{NewVar nm} fl tl cont
    let tyAscr = if !chooseAny then ":" <++> printTy ty else empty
    let declPref = case mut of
                     Mutable   => "var"
                     Immutable => "val"
    let lhs = declPref <++> line nm <+> tyAscr <++> "="
    rhs <- printExpr Open initial
    pure $ flip vappend rest $ hangSep' 2 lhs rhs

  printStmts fl tl $ NewF sig body cont = do
    (nm ** _) <- genNewName fl _ _ names
    isInfix <- chooseAny
    let (isInfix ** infixCond) : (b ** So (not b || sig.From.length >= 1)) = case decSo _ of
                                                                               Yes condMet => (isInfix ** condMet)
                                                                               No _        => (False ** Oh)
    rest <- printStmts @{NewFun {isInfix} {infixCond} nm} fl tl cont
    (namesInside, funArgs) <- newVars fl _ names
    brBody <- chooseAny
    funBody <- if brBody
                 then printStmts @{namesInside} fl False body
                 else printSubStmts @{namesInside} fl True body
    flip vappend rest <$> do
      showResTy <- chooseAnyOf Bool
      tryLam <- chooseAnyOf Bool
      let funArgs = reverse (toList funArgs) <&> \(n, ty) => line n <+> ":" <++> printTy ty
      let defTail : List (Doc opts) -> Doc opts
          defTail funArgs = "def" <++> line nm <+> tuple funArgs <+> (if showResTy then ":" <++> printMaybeTy sig.To else empty) <++> "="
      let lamTail : List (Doc opts) -> Doc opts
          lamTail funArgs = "val" <++> line nm <++> "=" <++> tuple funArgs <++> "=>"
      let (extPref, funSig) = case (isInfix, funArgs) of
                     (True, head::funArgs) => (Just $ "extension" <++> parens head, defTail funArgs)
                     _                     => (Nothing, if tryLam then lamTail funArgs else defTail funArgs)
      let br = brBody || tryLam && showResTy && not (isRet body)
      let endingTypeAsc = tryLam && showResTy
      let funBody' = parenthesise (endingTypeAsc && not br) funBody
      let mainDef = wrapBrIf br funSig funBody' <+?+> whenTs endingTypeAsc (":" <++> printMaybeTy sig.To)
      pure $ case extPref of
        Nothing      => mainDef
        Just extPref => hangSep' 2 extPref mainDef

  printStmts fl tl $ (#=) n v cont = pure $ wrapMain tl $ flip vappend !(printStmts fl False cont) $
    line (varName {funs} n) <++> "=" <++> !(printExpr Open v)

  printStmts fl tl $ If cond th el cont = do
    rest <- printStmts fl False cont
    br <- chooseAny
    pure $ wrapMain tl $ flip vappend rest $ vsep $
      [ "if" <++> !(printExpr Open cond) <++> "then" <+> whenTs br " {"
      , indentE 2 !(printSubStmts fl (not br) th)
      ] ++ whenTs (not (isNop el) || !chooseAny)
      [ whenTs br "} " <+> "else" <+> whenTs br " {"
      , indentE 2 !(printSubStmts fl (not br) el)
      ] ++ whenTs br ["}"]

  printStmts fl tl $ Call n args cont = wrapMain tl <$> [| printFunCall Open n args `vappend` printStmts fl False cont |]

  printStmts fl tl $ Ret x = wrapMain tl <$> printExpr Open x

  printStmts fl tl $ Nop = pure $ wrapMain tl empty

  export
  printScala3 : {funs : _} -> {vars : _} -> {retTy : _} -> {opts : _} ->
                (names : UniqNames funs vars) =>
                (newNames : Gen0 String) =>
                Fuel ->
                Stmts funs vars retTy -> Gen0 $ Doc opts
  printScala3 fl = printStmts {names} {newNames} fl True

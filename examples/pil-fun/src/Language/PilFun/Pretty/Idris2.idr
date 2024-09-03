module Language.PilFun.Pretty.Idris2

import Data.Alternative
import Data.Fuel
import Data.SnocList
import public Data.So
import Data.Vect

import public Language.PilFun
import public Language.PilFun.Pretty

import Test.DepTyCheck.Gen

import public Text.PrettyPrint.Bernardy

import System.Random.Pure.StdGen

%default total

NamesRestrictions where
  reservedKeywords = fromList [
    "**", ",", "->", ".", "..", ".[|", ":", "; _", ";", "<-", "=", "=>",
    "@", "[|", "\\", "_", "{", "|]", "}", "$=", "as", "auto", "case", "covering", "data", "default", "Delay",
    "do", "else", "export", "forall", "Force", "if", "import", "impossible", "in", "infix", "infixl", "infixr",
    "let", "module", "namespace", "of", "partial", "prefix", "private", "proof", "public", "record", "rewrite",
    "then", "total", "where", "with", "main", "IO", "Int", "Bool"]

alphaNames : Gen0 String
alphaNames = pack <$> listOf {length = choose (1,10)} (choose ('a', 'z'))

infixNames : Gen0 String
infixNames = pack <$> listOf {length = choose (1,4)} (elements 
  [':', '+', '-', '*', '\\', '/', '=', '.', '?', '|', '&', '>', '<', '!', '@', '$', '%', '^', '~', '#'])

printTy : Ty -> Doc opts
printTy Int' = "Int"
printTy Bool' = "Bool"

printMaybeTy : MaybeTy -> Doc opts
printMaybeTy Nothing   = "()"
printMaybeTy $ Just ty = printTy ty

printExpr : {funs : _} -> {vars : _} -> {opts : _} ->
            (names : UniqNames Idris2 funs vars) =>
            Expr funs vars ty -> Gen0 $ Doc opts

printFunCall : {funs : _} -> {vars : _} -> {opts : _} ->
               (names : UniqNames Idris2 funs vars) =>
               IndexIn funs -> ExprsSnocList funs vars argTys -> Gen0 $ Doc opts

printFunCall n args = do
    let f_name = funName {vars} n
    let f_doc : Doc opts = line f_name
    let arExps = toList $ getExprs args
    let preparedArgs : List (Exists (Expr funs vars)) -> Gen0 $ Doc opts = 
        \as => map hsep $ for as $ \(Evidence _ e) => printExpr e
    pure $ hangSep' 2 f_doc !(preparedArgs arExps)

printExpr $ C $ I k = pure $ line $ show k
printExpr $ C $ B False = pure "False"
printExpr $ C $ B True = pure "True"
printExpr $ V n = case index vars n of
    (_, Mutable) => pure $ "!" <+> (parenthesise True $ "readIORef" <++> line (varName {funs} n))
    (_, Immutable) => pure $ line $ varName {funs} n
printExpr @{uniqNames} $ F n args = do 
  funCallDoc <- assert_total printFunCall n args
  let proccesedDoc = parenthesise True funCallDoc
  let finalDoc = if isFunPure @{uniqNames} n then proccesedDoc else ("!" <+> proccesedDoc)
  pure finalDoc

printStmts : {funs : _} -> {vars : _} -> {retTy : _} -> {opts : _} ->
             (names : UniqNames Idris2 funs vars) =>
             Fuel ->
             Stmts funs vars retTy -> Gen0 $ Doc opts

printStmts fl $ NewV ty Immutable initial cont = do
  (nm ** _) <- genNewName fl alphaNames _ _ names
  rest <- printStmts @{NewVar nm} fl cont
  let lhs = "let" <++> line nm <++> "="
  rhs <- printExpr initial
  pure $ flip vappend rest $ hangSep' 2 lhs rhs

printStmts fl $ NewV ty Mutable initial cont = do
  (nm ** _) <- genNewName fl alphaNames _ _ names
  rest <- printStmts @{NewVar nm} fl cont
  let lhs = line nm <++> "<-"
  rhs <- printExpr initial
  pure $ flip vappend rest $ hangSep' 2 lhs $ "newIORef" <++> rhs

printStmts fl $ NewF (typesFrom ==> maybeRet) body cont = do
  (nm ** _) <- genNewName fl alphaNames _ _ names
  rest <- printStmts @{NewFun nm} fl cont
  let processedInputTypes = hsep $ (snocListTyToList typesFrom) <&> (\ty => printTy ty <++> "->")
  let processedOutputType = "IO" <++> printMaybeTy maybeRet
  let idrisTypeSignature = processedInputTypes <++> processedOutputType
  (namesInside, funArgs) <- newVars fl alphaNames _ names
  let prerparedArgs = hsep $ reverse (toList funArgs) <&> \(n, t) => line n
  body <- printStmts @{namesInside} fl body <&> indent' 6
  pure $ flip vappend rest $ vsep 
    [ "let" <++> line nm <++> ":" <++> idrisTypeSignature,
      indent 4 $ line nm <++> prerparedArgs <++> "=" <++> "do", 
      body ]

printStmts fl $ (#=) n v cont = do
    v_doc <- printExpr v
    rest <- printStmts fl cont
    pure $ flip vappend rest $ line "writeIORef" <++> line (varName {funs} n) <++> v_doc

printStmts fl $ If cond th el cont = do
    rest <- printStmts fl cont
    condExprDoc <- printExpr cond
    thenDoc <- printStmts fl th
    elseDoc <- printStmts fl el
    pure $ flip vappend rest $ vsep ["if" <++> condExprDoc <++> "then do", indent' 4 thenDoc, indent 2 "else do", indent' 6 elseDoc]

printStmts fl $ Call n args cont = do
    rest <- printStmts fl cont
    pure $ flip vappend rest $ !(printFunCall n args)

printStmts fl $ Ret expr = do
    exprDoc <- printExpr expr
    pure $ "pure" <++> exprDoc

printStmts fl $ Nop = pure "pure ()"

export
printIdris2 : {funs : _} -> {vars : _} -> {retTy : _} -> {opts : _} ->
              (names : UniqNames Idris2 funs vars) =>
              Fuel ->
              Stmts funs vars retTy -> Gen0 $ Doc opts
printIdris2 fl stmts = do
    pure $ vsep ["module Main", 
                 "",
                 "import Data.IORef",
                 "",
                 "main : IO ()",
                 "main = do",
                 indent' 2 $ !(printStmts fl stmts)]

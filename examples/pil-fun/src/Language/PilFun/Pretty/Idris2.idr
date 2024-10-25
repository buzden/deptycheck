module Language.PilFun.Pretty.Idris2

import Data.Alternative
import Data.Fuel
import Data.SnocList
import public Data.So
import Data.Vect
import Data.String

import public Language.PilFun
import public Language.PilFun.Pretty

import Test.DepTyCheck.Gen

import public Text.PrettyPrint.Bernardy

import System.Random.Pure.StdGen

%default total

NamesRestrictions where
  reservedKeywords = fromList [
    "**", ",", "->", ".", "..", ".[|", ":", "; _", ";", "<-", "=", "=>", "%", "=", "===", "!", "&",
    "@", "[|", "\\", "_", "{", "|]", "}", "$=", "as", "auto", "case", "covering", "data", "default", "Delay",
    "do", "else", "export", "forall", "Force", "if", "import", "impossible", "in", "infix", "infixl", "infixr",
    "let", "module", "namespace", "of", "partial", "prefix", "private", "proof", "public", "record", "rewrite",
    "then", "total", "where", "with", "main", "IO", "Int", "Bool"]

alphaNames : Gen0 String
alphaNames = pack <$> listOf {length = choose (1,10)} (choose ('a', 'z'))

infixNames : Gen0 String
infixNames = flip suchThat (not . isPrefixOf "--") $ pack <$> listOf {length = choose (1,4)} (elements 
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

printFunCall : {funs : _} -> {vars : _} -> {from : _} -> {to : _} -> {opts : _} ->
               (names : UniqNames Idris2 funs vars) =>
               (n : IndexIn funs) -> 
               (ati : AtIndex funs n (from ==> to)) => 
               ExprsSnocList funs vars from -> Gen0 $ Doc opts

data ArgStruct : LayoutOpts -> Type where
  InfixTwoArgs : {opts : _} -> Doc opts -> Doc opts -> ArgStruct opts
  PrefixTwoArgs : {opts : _} -> Doc opts -> Doc opts -> ArgStruct opts
  ManyArgs : {opts : _} -> List (Doc opts) -> ArgStruct opts
  NoArgs : {opts : _} -> ArgStruct opts

getArgs : {from' : SnocListTy} ->
          {to' : MaybeTy} ->
          (argFs : Funs ** argVs : Vars ** argNms : UniqNames Idris2 argFs argVs ** ExprsSnocList argFs argVs from') ->
          {fs : Funs} ->
          {vs : Vars} ->
          (nms : UniqNames Idris2 fs vs) -> 
          (i : IndexIn fs) ->
          (ati : AtIndex fs i (from' ==> to')) ->
          {opts : _} ->
          Gen0 (ArgStruct opts)

getArgs (_ ** _ ** _ ** [<]) _ _ _ = pure NoArgs

getArgs argedLst (JustNew _ {ss}) i ati = getArgs argedLst ss i ati
getArgs argedLst (NewVar _ {ss}) i ati = getArgs argedLst ss i ati

getArgs argedLst (NewFun _ {ss}) (There i) (There' i') = getArgs argedLst ss i i'

getArgs {from'} argedLst (NewFun _ {languageCondition}) Here Here' with (languageCondition)

  getArgs {from'} argedLst (NewFun _ {languageCondition}) Here Here' | Idris2Cond (IsInfix (a ** b ** to ** rst) isPure) with (rst)
    getArgs {from' = [< a, b ]} (argFs ** argVs ** argNms ** [< a', b' ]) (NewFun _ {languageCondition}) Here Here' | Idris2Cond (IsInfix (a ** b ** to ** Refl) isPure) | Refl = do 
      aDoc <- printExpr a'
      bDoc <- printExpr b'
      pure $ InfixTwoArgs aDoc bDoc

  getArgs {from'} argedLst (NewFun _ {languageCondition}) Here Here' | Idris2Cond (NotInfix isPure) with (from')
    _ | [< a, b ] with (argedLst)
      _ | (_ ** _ ** _ ** [< a', b' ]) = do
          aDoc <- printExpr a'
          bDoc <- printExpr b'
          pure $ PrefixTwoArgs aDoc bDoc
    _ | from'' with (argedLst)
      _ | (_ ** _ ** _ ** lst) = do
          argsDocs : List (Doc _) <- for ((toList . getExprs) lst) (\(Evidence _ e) => printExpr e)
          pure $ ManyArgs argsDocs


printFunCall n args = do
  wantInfix <- chooseAnyOf Bool
  let f_name = funName {vars} n
  let f_doc : Doc opts = line f_name
  processedArgs <- getArgs (funs ** vars ** names ** args) names n ati
  case (wantInfix, processedArgs) of
    (True, InfixTwoArgs a b) => pure $ a <++> f_doc <++> b
    (False, InfixTwoArgs a b) => pure $ "(" <+> f_doc <+> ")" <++> a <++> b
    (True, PrefixTwoArgs a b) => pure $ a <++> "`" <+> f_doc <+> "`" <++> b
    (False, PrefixTwoArgs a b) => pure $ f_doc <++> a <++> b
    (_, ManyArgs argsDocs) => pure $ f_doc <++> hsep argsDocs
    (_, NoArgs)=> pure f_doc
      
printExpr $ C $ I k = pure $ line $ show k
printExpr $ C $ B False = pure "False"
printExpr $ C $ B True = pure "True"
printExpr $ V n = case index vars n of
  (_, Mutable) => pure $ "!" <+> (parenthesise True $ "readIORef" <++> line (varName {funs} n))
  (_, Immutable) => pure $ line $ varName {funs} n
printExpr @{uniqNames} $ F {from = [<]} n args = do 
  funCallDoc <- assert_total printFunCall n args
  let finalDoc = if isFunPure uniqNames n then funCallDoc else ("!" <+> funCallDoc)
  pure finalDoc
printExpr @{uniqNames} $ F {from} n args = do 
  funCallDoc <- assert_total printFunCall n args
  let proccesedDoc = parenthesise True funCallDoc
  let finalDoc = if isFunPure uniqNames n then proccesedDoc else ("!" <+> proccesedDoc)
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

printStmts fl $ NewF ([<] ==> maybeRet) body cont = do
  let (isInfix ** infixCond) : (b ** IdrisCondition ([<] ==> maybeRet) b False) = (False ** NotInfix False)
  (nm ** _) <- genNewName fl alphaNames _ _ names
  rest <- printStmts @{NewFun nm {isInfix}} fl cont
  let funName = line nm
  let processedOutputType = "IO" <++> printMaybeTy maybeRet
  printedBody <- printStmts fl body <&> indent' 6
  pure $ flip vappend rest $ vsep 
    [ "let" <++> funName <++> ":" <++> processedOutputType,
      indent 4 $ funName <++> "=" <++> "do", 
      printedBody ]

printStmts fl $ NewF ([< a, b ] ==> maybeRet) body cont = do
  wantInfix <- chooseAnyOf Bool
  let (isInfix ** infixCond) : (inf ** IdrisCondition ([< a, b ] ==> maybeRet) inf False) = case wantInfix of 
        True => (True ** IsInfix (a ** b ** maybeRet ** Refl) False) 
        False => (False ** NotInfix False)
  let nameGen = if isInfix then infixNames else alphaNames
  (nm ** _) <- genNewName fl nameGen _ _ names
  rest <- printStmts @{NewFun nm {isInfix} @{names}} fl cont
  let infixAwareName : Doc opts = if isInfix then "(" <+> line nm <+> ")" else line nm
  let processedInputTypes : Doc opts = hsep $ (snocListTyToList [< a, b ]) <&> (\ty => printTy ty <++> "->")
  let processedOutputType = "IO" <++> printMaybeTy maybeRet
  let idrisTypeSignature = processedInputTypes <++> processedOutputType
  (namesInside, funArgs) <- newVars fl alphaNames [< a, b ] (JustNew @{names} nm)
  let prerparedArgs = hsep $ reverse (toList funArgs) <&> \(n, t) => line n
  printedBody <- printStmts @{namesInside} fl body <&> indent' 6
  let declAndDefintion = [ "let" <++> infixAwareName <++> ":" <++> idrisTypeSignature,
                            indent 4 $ infixAwareName <++> prerparedArgs <++> "=" <++> "do", 
                            printedBody ]
  let final = if isInfix then ("let infix 1" <++> line nm) :: declAndDefintion else declAndDefintion
  pure $ flip vappend rest $ vsep final

printStmts fl $ NewF (typesFrom ==> maybeRet) body cont = do
  let (isInfix ** infixCond) : (b ** IdrisCondition (typesFrom ==> maybeRet) b False) = (False ** NotInfix False)
  (nm ** _) <- genNewName fl alphaNames _ _ names
  rest <- printStmts @{NewFun nm {isInfix} @{names}} fl cont
  let funName = line nm
  let processedInputTypes : Doc opts = hsep $ (snocListTyToList typesFrom) <&> (\ty => printTy ty <++> "->")
  let processedOutputType = "IO" <++> printMaybeTy maybeRet
  let idrisTypeSignature = processedInputTypes <++> processedOutputType
  (namesInside, funArgs) <- newVars fl alphaNames _ (JustNew @{names} nm)
  let prerparedArgs = hsep $ reverse (toList funArgs) <&> \(n, t) => line n
  printedBody <- printStmts @{namesInside} fl body <&> indent' 6
  let declAndDefintion = vsep [ "let" <++> funName <++> ":" <++> idrisTypeSignature,
                                indent 4 $ funName <++> prerparedArgs <++> "=" <++> "do", 
                                printedBody ]
  pure $ vappend declAndDefintion rest

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

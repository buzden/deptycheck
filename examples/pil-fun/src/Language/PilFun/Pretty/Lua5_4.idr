module Language.PilFun.Pretty.Lua5_4

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

printTy : Ty -> Doc opts
printTy Int'  = "number"
printTy Bool' = "boolean"

printMaybeTy : MaybeTy -> Doc opts
printMaybeTy Nothing   = "nil"
printMaybeTy $ Just ty = printTy ty

unaryOps : List String
unaryOps = ["+", "-", "#", "~", "not"]

-- isUnaryOp : String -> List arg -> Bool
-- isUnaryOp str xs = elem str unaryOps && length xs == 1

NamesRestrictions where
  reservedKeywords = fromList
    [ "and",       "break",     "do",        "else",      "elseif",    "end"
    , "false",     "for",       "function",  "goto",      "if",        "in"
    , "local",     "nil",       "not",       "or",        "repeat",    "return"
    , "then",      "true",      "until",     "while"
    ]

-- printFunCall p n args = do
--   let fn = funName {vars} n
--   let f = line fn
--   let args = toList $ getExprs args
--   let tupledArgs = \as => map tuple $ for as $ \(Evidence _ e) => printExpr Open e
--   case (isFunInfix @{names} n, args, !(chooseAnyOf Bool)) of
--     -- Call for bitwise infix extension method
--     (True, [Evidence _ l, Evidence _ r], True) => pure $ parenthesise (p >= App) $ !(printExpr App l) <++> f <++> !(printExpr App r)
--     -- Call for appropriate extension method with 0, 2 or more arguments
--     (True, Evidence _ head :: args, _) => pure $ parenthesise (p >= App) $ !(printExpr App head) <+> "." <+> f <+> !(tupledArgs args)
--     -- Call for normal function
--     _ => pure $ parenthesise (p >= App && isUnaryOp fn args) $ hang' 2 f !(tupledArgs args)

-- printExpr p $ C $ I k     = pure $ line $ show k
-- printExpr p $ C $ B False = pure $ "false"
-- printExpr p $ C $ B True  = pure $ "true"
-- printExpr p $ V n         = pure $ line $ varName {funs} n
-- printExpr p $ F n args    = assert_total printFunCall p n args


-- printSubStmts : {funs : _} -> {vars : _} -> {retTy : _} -> {opts : _} ->
--                 (names : UniqNames funs vars) =>
--                 (newNames : Gen0 String) =>
--                 Fuel ->
--                 (noEmpty : Bool) ->
--                 Stmts funs vars retTy -> Gen0 $ Doc opts
-- printSubStmts _  True Nop = pure "{}"
-- printSubStmts fl _    ss  = printStmts fl False ss

-- printStmts fl tl $ NewF sig body cont = do
--   (nm ** _) <- genNewName fl _ _ names
--   isInfix <- chooseAny
--   let (isInfix ** infixCond) : (b ** So (not b || sig.From.length >= 1)) = case decSo _ of
--                                                                              Yes condMet => (isInfix ** condMet)
--                                                                              No _        => (False ** Oh)
--   rest <- printStmts @{NewFun {isInfix} {infixCond} nm} fl tl cont
--   (namesInside, funArgs) <- newVars fl _ names
--   brBody <- chooseAny
--   funBody <- if brBody
--                then printStmts @{namesInside} fl False body
--                else printSubStmts @{namesInside} fl True body
--   flip vappend rest <$> do
--     showResTy <- chooseAnyOf Bool
--     tryLam <- chooseAnyOf Bool
--     let funArgs = reverse (toList funArgs) <&> \(n, ty) => line n <+> ":" <++> printTy ty
--     let defTail : List (Doc opts) -> Doc opts
--         defTail funArgs = "def" <++> line nm <+> tuple funArgs <+> (if showResTy then ":" <++> printMaybeTy sig.To else empty) <++> "="
--     let lamTail : List (Doc opts) -> Doc opts
--         lamTail funArgs = "val" <++> line nm <++> "=" <++> tuple funArgs <++> "=>"
--     let (extPref, funSig) = case (isInfix, funArgs) of
--                    (True, head::funArgs) => (Just $ "extension" <++> parens head, defTail funArgs)
--                    _                     => (Nothing, if tryLam then lamTail funArgs else defTail funArgs)
--     let br = brBody || tryLam && showResTy && not (isRet body)
--     let endingTypeAsc = tryLam && showResTy
--     let funBody' = parenthesise (endingTypeAsc && not br) funBody
--     let mainDef = wrapBrIf br funSig funBody' <+?+> when endingTypeAsc (":" <++> printMaybeTy sig.To)
--     pure $ case extPref of
--       Nothing      => mainDef
--       Just extPref => hangSep' 2 extPref mainDef

-- printStmts fl tl $ Call n args cont = wrapMain fl tl (Just cont) $ printFunCall Open n args

printExpr : {funs : _} -> {vars : _} -> {opts : _} ->
            (names : UniqNames funs vars) =>
            Expr funs vars ty -> Gen0 $ Doc opts
printFunCall : {funs : _} -> {vars : _} -> {opts : _} ->
               (names : UniqNames funs vars) =>
               IndexIn funs -> ExprsSnocList funs vars argTys -> Gen0 $ Doc opts

printStmts : {funs : _} -> {vars : _} -> {retTy : _} -> {opts : _} ->
             (names : UniqNames funs vars) =>
             (newNames : Gen0 String) =>
             Fuel ->
             Stmts funs vars retTy -> Gen0 $ Doc opts

printExpr (C $ I x) = pure $ line $ show x
printExpr (C $ B True) = pure $ line "true"
printExpr (C $ B False) = pure $ line "false"
printExpr (V n) = pure $ line $ varName {funs} n
printExpr (F n x) = printFunCall n x

printFunCall _ _ = pure $ line "<call>"

newVarLhv : {opts : _} -> (name : String) -> (mut : Mut) -> Gen0 $ Doc opts
newVarLhv name mut = do
  let attr = case mut of
                  Mutable => empty
                  Immutable => space <+> angles (line "const")
  addLocal <- case mut of
                   Mutable => chooseAnyOf Bool
                   Immutable => pure $ True
  let local = if addLocal then line "local" <+> space else empty
  pure $ local <+> line name <+> attr


withCont : {opts : _} -> (cont : Doc opts) -> (stmt : Doc opts) -> Gen0 (Doc opts)
withCont cont stmt =
  pure $ stmt `vappend` cont

printStmts fuel (NewV ty mut initial cont) = do
  (name ** _) <- genNewName fuel _ _ names
  lhv <- newVarLhv name mut
  rhv <- printExpr initial
  withCont !(printStmts fuel cont) $ hangSep' 2 (lhv <++> line "=") rhv

printStmts fuel (NewF sig body cont) = do
  (name ** _) <- genNewName fuel _ _ names
  cont' <- printStmts fuel cont
  isLambda <- chooseAnyOf Bool
  withCont cont' $ line "new func" <++> line name

printStmts fuel ((#=) lhv rhv cont) = do
  let lhv' = line (varName {funs} lhv) <++> "="
  rhv' <- printExpr rhv
  withCont !(printStmts fuel cont) $ hangSep' 2 lhv' rhv'

printStmts fuel (If cond th el cont) = do
  cond' <- printExpr cond
  th' <- printStmts fuel th
  let skipElse = isNop el && !(chooseAnyOf Bool)
  el' <- if skipElse
            then pure empty
            else do
              body <- printStmts @{names} @{newNames} fuel el
              pure $ line "else" `vappend` indent' 2 body
  let top = hangSep 0 (line "if" <++> cond') (line "then")
  withCont !(printStmts fuel cont) $ vsep
    [ top
    , indent' 2 th'
    , el'
    , line "end"
    ]

printStmts fuel (Call n x cont) = do
  call <- printFunCall n x
  withCont !(printStmts fuel cont) call

printStmts fuel (Ret res) =
  pure $ line "return" <++> !(printExpr res)

printStmts fuel Nop = do
  useSemicolon <- chooseAnyOf Bool
  if useSemicolon then pure $ line ";"
                  else pure empty

export
printLua5_4 : PP
printLua5_4 fl = printStmts {names} {newNames} fl

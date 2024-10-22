module Language.PilFun.Pretty.Lua5_4

import Data.Fuel
import Data.List
import Data.Maybe
import Data.SnocList
import Data.Vect

import public Language.PilFun
import public Language.PilFun.Pretty

import Test.DepTyCheck.Gen

import public Text.PrettyPrint.Bernardy

%default total

printTy : Ty -> Doc opts
printTy Int'  = "number"
printTy Bool' = "boolean"

NamesRestrictions where
  reservedKeywords = fromList
    [ "and",       "break",     "do",        "else",      "elseif",    "end"
    , "false",     "for",       "function",  "goto",      "if",        "in"
    , "local",     "nil",       "not",       "or",        "repeat",    "return"
    , "then",      "true",      "until",     "while"
    ]

Priority : Type
Priority = Fin 12

priorities : List (String, Priority)
priorities = [ ("or", 11)
             , ("and", 10)
             , ("<", 9), (">", 9), ("<=", 9), (">=", 9), ("~=", 9), ("==", 9)
             , ("|", 8)
             , ("~", 7)
             , ("&", 6)
             , ("<<", 5), (">>", 5)
             , ("..", 4)
             , ("+", 3), ("-", 3)
             , ("*", 2), ("/", 2), ("//", 2), ("%", 2)
             , ("not", 1), ("#", 1), ("-", 1), ("~", 1)
             , ("^", 0)
             ]

priority : String -> Maybe Priority
priority func = lookup func priorities

printExpr : {funs : _} -> {vars : _} -> {opts : _} ->
            (names : UniqNames funs vars) =>
            Fuel ->
            (lastPriority : Maybe Priority) ->
            Expr funs vars ty -> Gen0 $ Doc opts
printFunCall : {funs : _} -> {vars : _} -> {opts : _} ->
               (names : UniqNames funs vars) =>
               Fuel ->
               (lastPriority : Maybe Priority) ->
               IndexIn funs -> ExprsSnocList funs vars argTys ->
               Gen0 $ Doc opts
printStmts : {funs : _} -> {vars : _} -> {retTy : _} -> {opts : _} ->
             (names : UniqNames funs vars) =>
             (newNames : Gen0 String) =>
             Fuel ->
             Stmts funs vars retTy -> Gen0 $ Doc opts

printExpr fuel _ (C $ I x) = pure $ line $ show x
printExpr fuel _ (C $ B True) = pure "true"
printExpr fuel _ (C $ B False) = pure "false"
printExpr fuel _ (V n) = pure $ line $ varName {funs} n
printExpr fuel lastPrior (F n x) = printFunCall fuel lastPrior n x

addCommas : {opts : _} -> List (Doc opts) -> List (Doc opts)
addCommas [] = []
addCommas [x] = [x]
addCommas (x::xs) = (x <+> comma) :: addCommas xs

printFunCall fuel lastPrior fun args = do
  let name = funName {vars} fun
  let thisPrior = priority name
  let addParens = !(chooseAnyOf Bool)
                   || isJust lastPrior && thisPrior >= lastPrior
  args' <- for (toList $ getExprs args) (\(Evidence _ e) => assert_total printExpr fuel Nothing e)
  case (isFunInfix @{names} fun, args') of
    (True, [lhv, rhv]) => do
       pure $ parenthesise addParens $ hangSep 2 (lhv <++> line name) rhv
    (_, [x]) => do
       -- note: two minus signs may be interpreted as a comment
       pure $ parenthesise addParens $ line name
         <+> when (name == "not" || name == "-") space
         <+> x
    (_, _) => do
      let argsWithCommas = sep' $ addCommas args'
      let applyShort = line name <+> "(" <+> argsWithCommas <+> ")"
      let applyLong = vsep [ line name <+> "("
                           , indent 2 argsWithCommas
                           , ")"
                           ]
      pure $ ifMultiline applyShort applyLong

newVarLhv : {opts : _} -> (name : String) -> (mut : Mut) -> Gen0 $ Doc opts
newVarLhv name mut = do
  let attr = case mut of
               Mutable => empty
               Immutable => space <+> angles "const"
  pure $ "local" <++> line name <+> attr

withCont : {opts : _} -> (cont : Doc opts) -> (stmt : Doc opts) -> Gen0 (Doc opts)
withCont cont stmt =
  pure $ stmt `vappend` cont

printStmts fuel (NewV ty mut initial cont) = do
  (name ** _) <- genNewName fuel _ _ names
  lhv <- newVarLhv name mut
  rhv <- printExpr fuel Nothing initial
  withCont !(printStmts fuel cont) $ hangSep' 2 (lhv <++> "=") rhv

printStmts fuel (NewF sig body cont) = do
  (name ** _) <- genNewName fuel _ _ names
  (localNames, funArgs) <- newVars fuel _ names
  let funArgs' = reverse (toList funArgs)
  let argHints = funArgs' <&> \(name, ty) =>
                 the (Doc opts) "---@param" <++> line name <++> printTy ty
  let hints = vsep $ case sig.To of
                Just retTy => argHints ++ ["---@return" <++> printTy retTy]
                Nothing => argHints
  let argNames = funArgs' <&> \(name, _) => the (Doc opts) (line name)
  let argList = sep' $ addCommas argNames
  let fnHeaderShort = "local" <++> "function" <++> (line name) <+>
                      "(" <+> argList <+> ")"
  let fnHeaderLong = vsep [ "function" <++> (line name) <+> "("
                          , indent 2 argList
                          , ")"
                          ]
  let fnHeader = ifMultiline fnHeaderShort fnHeaderLong
  fnBody <- printStmts @{localNames} fuel body
  cont' <- printStmts fuel cont
  withCont cont' $ vsep [ hints
                        , fnHeader
                        , indent' 2 fnBody
                        , "end"
                        ]

printStmts fuel ((#=) lhv rhv cont) = do
  let lhv' = line (varName {funs} lhv) <++> "="
  rhv' <- printExpr fuel Nothing rhv
  withCont !(printStmts fuel cont) $ hangSep' 2 lhv' rhv'

printStmts fuel (If cond th el cont) = do
  cond' <- printExpr fuel Nothing cond
  th' <- printStmts fuel th
  let skipElse = isNop el && !(chooseAnyOf Bool)
  el' <- if skipElse
           then pure empty
           else do
             body <- printStmts @{names} @{newNames} fuel el
             pure $ "else" `vappend` indent' 2 body
  let top = hangSep 0 ("if" <++> cond') "then"
  withCont !(printStmts fuel cont) $ vsep
    [ top
    , indent' 2 th'
    , el'
    , "end"
    ]

printStmts fuel (Call n x cont) = do
  call <- printFunCall fuel Nothing n x
  withCont !(printStmts fuel cont) call

printStmts fuel (Ret res) =
  pure $ "return" <++> !(printExpr fuel Nothing res)

printStmts fuel Nop = do
  useSemicolon <- chooseAnyOf Bool
  if useSemicolon
    then pure ";"
    else pure empty

export
printLua5_4 : PP
printLua5_4 fl = printStmts {names} {newNames} fl

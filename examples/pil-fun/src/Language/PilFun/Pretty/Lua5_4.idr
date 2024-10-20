module Language.PilFun.Pretty.Lua5_4

import Data.Alternative
import Data.Fuel
import Data.SnocList
import public Data.So
import Data.Vect
import Data.List

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
            Expr funs vars ty -> Gen0 $ Doc opts
printFunCall : {funs : _} -> {vars : _} -> {opts : _} ->
               (names : UniqNames funs vars) =>
               (lastPriority : Maybe Priority) ->
               IndexIn funs -> ExprsSnocList funs vars argTys ->
               Gen0 $ Doc opts
printStmts : {funs : _} -> {vars : _} -> {retTy : _} -> {opts : _} ->
             (names : UniqNames funs vars) =>
             (newNames : Gen0 String) =>
             Fuel ->
             Stmts funs vars retTy -> Gen0 $ Doc opts

printExpr (C $ I x) = pure $ line $ show x
printExpr (C $ B True) = pure $ line "true"
printExpr (C $ B False) = pure $ line "false"
printExpr (V n) = pure $ line $ varName {funs} n
printExpr (F n x) = printFunCall Nothing n x

addCommas : {opts : _} -> List (Doc opts) -> List (Doc opts)
addCommas [] = []
addCommas [x] = [x]
addCommas (x::xs) = (x <+> comma) :: addCommas xs

printFunCall _ _ _ = pure $ line "<call>"

newVarLhv : {opts : _} -> (name : String) -> (mut : Mut) -> Gen0 $ Doc opts
newVarLhv name mut = do
  let attr = case mut of
                  Mutable => empty
                  Immutable => space <+> angles (line "const")
  pure $ line "local" <++> line name <+> attr

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
  (localNames, funArgs) <- newVars fuel _ names
  let argNames = reverse (toList funArgs) <&>
                 \(name, _) => the (Doc opts) (line name)
  let argList = sep' $ addCommas argNames
  let fnHeaderShort = line "function" <++> (line name) <+>
                      line "(" <+> argList <+> line ")"
  let fnHeaderLong = vsep [ line "function" <++> (line name) <+> line "("
                          , indent 2 argList
                          , line ")"
                          ]
  let fnHeader = ifMultiline fnHeaderShort fnHeaderLong
  fnBody <- printStmts @{localNames} fuel body
  cont' <- printStmts fuel cont
  withCont cont' $ vsep [ fnHeader
                        , indent' 2 fnBody
                        , line "end"
                        ]

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
  call <- printFunCall Nothing n x
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

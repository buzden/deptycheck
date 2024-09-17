-- Common definitions for all pretty-printers
module Language.PilFun.Pretty

import Data.Alternative
import Data.Fuel
import Data.SnocList
import public Data.So
import public Data.SortedSet
import Data.Vect

import public Language.PilFun

import Test.DepTyCheck.Gen

import public Text.PrettyPrint.Bernardy

import System.Random.Pure.StdGen

%default total

public export
data UniqNames : Funs -> Vars -> Type
public export
data NameIsNew : UniqNames funs vars -> String -> Type

data UniqNames : Funs -> Vars -> Type where
  Empty   : UniqNames [<] [<]
  JustNew : (ss : UniqNames funs vars) => (s : String) -> (0 _ : NameIsNew ss s) => UniqNames funs vars
  NewFun  : (ss : UniqNames funs vars) => (s : String) -> (0 _ : NameIsNew ss s) =>
            {default False isInfix : Bool} -> (0 infixCond : So $ not isInfix || fun.From.length >= 1) =>
            UniqNames (funs:<fun) vars
  NewVar  : (ss : UniqNames funs vars) => (s : String) -> (0 _ : NameIsNew ss s) => UniqNames funs ((:<) vars var mut)

data NameIsNew : UniqNames funs vars -> String -> Type where
  E : NameIsNew {funs=[<]} {vars=[<]} Empty x
  J : (0 _ : So $ x /= s) -> NameIsNew {funs} {vars} ss x -> NameIsNew {funs} {vars} (JustNew @{ss} s @{sub}) x
  F : (0 _ : So $ x /= s) -> NameIsNew {funs} {vars} ss x -> NameIsNew {funs=funs:<fun} {vars} (NewFun @{ss} {isInfix} s @{sub} @{infixCond}) x
  V : (0 _ : So $ x /= s) -> NameIsNew {funs} {vars} ss x -> NameIsNew {funs} {vars=(:<) vars var mut} (NewVar @{ss} s @{sub}) x

public export
interface NamesRestrictions where
  reservedKeywords : SortedSet String

rawNewName : Fuel -> (Fuel -> Gen MaybeEmpty String) =>
             (vars : Vars) -> (funs : Funs) -> (names : UniqNames funs vars) ->
             Gen MaybeEmpty (s ** NameIsNew names s)

export
genNewName : Fuel -> (Fuel -> Gen MaybeEmpty String) =>
             NamesRestrictions =>
             (funs : Funs) -> (vars : Vars) -> (names : UniqNames funs vars) ->
             Gen MaybeEmpty (s ** NameIsNew names s)
genNewName fl @{genStr} funs vars names = do
  nn@(nm ** _) <- rawNewName fl @{genStr} vars funs names
  if reservedKeywords `contains'` nm
    then assert_total $ genNewName fl @{genStr} funs vars names -- we could reduce fuel instead of `assert_total`
    else pure nn

varName : UniqNames funs vars => IndexIn vars -> String
varName @{JustNew @{ss} _} i         = varName @{ss} i
varName @{NewFun @{ss} _}  i         = varName @{ss} i
varName @{NewVar       s}  Here      = s
varName @{NewVar @{ss} _}  (There i) = varName @{ss} i

funName : UniqNames funs vars => IndexIn funs -> String
funName @{JustNew @{ss} _} i         = funName @{ss} i
funName @{NewFun       s}  Here      = s
funName @{NewFun @{ss} _}  (There i) = funName @{ss} i
funName @{NewVar @{ss} _}  i         = funName @{ss} i

isFunInfix : UniqNames funs vars => IndexIn funs -> Bool
isFunInfix @{JustNew @{ss} _} i        = isFunInfix @{ss} i
isFunInfix @{NewFun {isInfix} _} Here  = isInfix
isFunInfix @{NewFun @{ss} s} (There i) = isFunInfix @{ss} i
isFunInfix @{NewVar @{ss} s} i         = isFunInfix @{ss} i

-- Returned vect has a reverse order; I'd like some `SnocVect` here.
newVars : (newNames : Gen0 String) =>
          NamesRestrictions =>
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

wrapBrIf : {opts : _} -> (indeed : Bool) -> Doc opts -> Doc opts -> Doc opts
wrapBrIf False pre x = pre `vappend` indent' 2 x
wrapBrIf True pre x = ifMultiline (pre <++> "{" <++> x <++> "}") (vsep [pre <++> "{", indent' 2 x, "}"])

public export
0 PP : Type
PP = {funs : _} -> {vars : _} -> {retTy : _} -> {opts : _} ->
     (names : UniqNames funs vars) =>
     (newNames : Gen0 String) =>
     Fuel ->
     Stmts funs vars retTy -> Gen0 $ Doc opts

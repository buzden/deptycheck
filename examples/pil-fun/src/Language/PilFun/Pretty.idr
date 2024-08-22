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
data SupportedLanguages = Scala3
                        | Idris2

public export
ConditionType : Type
ConditionType = FunSig -> (isInfix : Bool) -> (isPure : Bool) -> Type

public export
data ScalaCondition : FunSig -> (isInfix : Bool) -> (isPure : Bool) -> Type
 where
  IsNotInfix : ScalaCondition funSig False b
  MoreThanOneArg : So (funSig.From.length >= 1) -> ScalaCondition funSig isInfix b

public export
data IdrisCondition : FunSig -> (isInfix : Bool) -> (isPure : Bool) -> Type
 where
  Trivial : IdrisCondition funSig isInfix isPure

public export
data LanguageToCondition : (l : SupportedLanguages) -> FunSig -> (isInfix : Bool) -> (isPure : Bool) -> Type
 where
  [search l]
  Scala3Cond : ScalaCondition funSig isInfix isPure -> LanguageToCondition Scala3 funSig isInfix isPure
  Idris2Cond : IdrisCondition funSig isInfix isPure -> LanguageToCondition Idris2 funSig isInfix isPure

public export
data UniqNames : (l : SupportedLanguages) -> (funs : Funs) -> (vars : Vars) -> Type
public export
data NameIsNew : (l : SupportedLanguages) -> (funs : Funs) -> (vars : Vars) -> UniqNames l funs vars -> String -> Type

data UniqNames : (l : SupportedLanguages) -> (funs : Funs) -> (vars : Vars) -> Type where
  [search funs vars]
  Empty   : UniqNames l [<] [<]
  JustNew : (ss : UniqNames l funs vars) => (s : String) -> (0 _ : NameIsNew l funs vars ss s) => UniqNames l funs vars
  NewFun  : (ss : UniqNames l funs vars) => (s : String) -> (0 _ : NameIsNew l funs vars ss s) =>
            {default False isInfix : Bool} -> {default False isPure : Bool} ->
            (0 languageCondition : LanguageToCondition l fun isInfix isPure) =>
            UniqNames l (funs:<fun) vars
  NewVar  : (ss : UniqNames l funs vars) => (s : String) -> (0 _ : NameIsNew l funs vars ss s) => UniqNames l funs ((:<) vars var mut)

data NameIsNew : (l : SupportedLanguages) -> (funs : Funs) -> (vars : Vars) -> UniqNames l funs vars -> String -> Type where
  E : NameIsNew l [<] [<] Empty x
  J : (0 _ : So $ x /= s) -> NameIsNew l funs vars ss x -> NameIsNew l funs vars (JustNew @{ss} s @{sub}) x
  F : (0 _ : So $ x /= s) -> NameIsNew l funs vars ss x -> NameIsNew l (funs:<fun) vars (NewFun @{ss} {isInfix} {isPure} s @{sub} @{infixCond}) x
  V : (0 _ : So $ x /= s) -> NameIsNew l funs vars ss x -> NameIsNew l funs ((:<) vars var mut) (NewVar @{ss} s @{sub}) x

public export
interface NamesRestrictions where
  reservedKeywords : SortedSet String

rawNewName : Fuel -> (l : SupportedLanguages) -> (Fuel -> Gen MaybeEmpty String) =>
             (funs : Funs) -> (vars : Vars) -> (names : UniqNames l funs vars) ->
             Gen MaybeEmpty (s ** NameIsNew l funs vars names s)

export
genNewName : {l : SupportedLanguages} -> Fuel -> (Fuel -> Gen MaybeEmpty String) =>
             NamesRestrictions =>
             (funs : Funs) -> (vars : Vars) -> (names : UniqNames l funs vars) ->
             Gen MaybeEmpty (s ** NameIsNew l funs vars names s)
genNewName fl @{genStr} funs vars names = do
  nn@(nm ** _) <- rawNewName fl l @{genStr} funs vars names
  if reservedKeywords `contains'` nm
    then assert_total $ genNewName fl @{genStr} funs vars names -- we could reduce fuel instead of `assert_total`
    else pure nn

varName : UniqNames l funs vars => IndexIn vars -> String
varName @{JustNew @{ss} _} i         = varName @{ss} i
varName @{NewFun @{ss} _}  i         = varName @{ss} i
varName @{NewVar       s}  Here      = s
varName @{NewVar @{ss} _}  (There i) = varName @{ss} i

funName : UniqNames l funs vars => IndexIn funs -> String
funName @{JustNew @{ss} _} i         = funName @{ss} i
funName @{NewFun       s}  Here      = s
funName @{NewFun @{ss} _}  (There i) = funName @{ss} i
funName @{NewVar @{ss} _}  i         = funName @{ss} i

isFunInfix : UniqNames l funs vars => IndexIn funs -> Bool
isFunInfix @{JustNew @{ss} _} i        = isFunInfix @{ss} i
isFunInfix @{NewFun {isInfix} _} Here  = isInfix
isFunInfix @{NewFun @{ss} s} (There i) = isFunInfix @{ss} i
isFunInfix @{NewVar @{ss} s} i         = isFunInfix @{ss} i

-- Returned vect has a reverse order; I'd like some `SnocVect` here.
newVars : (newNames : Gen0 String) =>
          NamesRestrictions =>
          {l : _} -> {funs : _} -> {vars : _} ->
          Fuel ->
          (extraVars : _) -> UniqNames l funs vars ->
          Gen0 (UniqNames l funs (vars ++ extraVars), Vect extraVars.length (String, Ty))
newVars _  [<]     names = pure (names, [])
newVars fl (vs:<v) names = do
  (names', vts) <- newVars fl vs names
  (nm ** _) <- genNewName {l} fl _ _ names'
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

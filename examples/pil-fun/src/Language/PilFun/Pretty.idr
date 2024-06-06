-- Common definitions for all pretty-printers
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

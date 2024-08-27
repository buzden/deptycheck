module Language.PilFun.Pretty.DSL

import public Data.So

import public Language.PilFun.Pretty

%default total

public export
record NamedCtxt (l : SupportedLanguages) where
  constructor MkNamedCtxt
  functions : Funs
  variables : Vars
  fvNames   : UniqNames l functions variables

public export %inline
AddFun : {0 l : SupportedLanguages} -> (isInfix : Bool) -> (isPure : Bool) -> (s : String) -> (fun : FunSig) ->
         (ctx : NamedCtxt l) ->
         (0 _ : LanguageToCondition l fun isInfix isPure) =>
         (0 _ : NameIsNew l ctx.functions ctx.variables ctx.fvNames s) =>
         NamedCtxt l
AddFun isInfix isPure s fun $ MkNamedCtxt funs vars names = MkNamedCtxt (funs:<fun) vars $ NewFun @{names} {isInfix} {isPure} {fun} s

public export %inline
(>>) : {0 arg : NamedCtxt l -> Type} -> {0 arg' : NamedCtxt l -> Type} -> 
       ((ctx : NamedCtxt l) -> (0 _ : arg ctx) => (0 _ : arg' ctx) => NamedCtxt l) -> 
       (ctx : NamedCtxt l) -> (0 _ : arg ctx) => (0 _ : arg' ctx) => NamedCtxt l
(>>) f x = f x

public export %inline
Enough : NamedCtxt l
Enough = MkNamedCtxt [<] [<] Empty

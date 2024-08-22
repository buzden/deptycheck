module Language.PilFun.Pretty.DSL

import public Data.So

import public Language.PilFun.Pretty

%default total

public export
record NamedCtxt where
  constructor MkNamedCtxt
  language : SupportedLanguages
  functions : Funs
  variables : Vars
  fvNames   : UniqNames language functions variables

public export %inline
AddFun : (isInfix : Bool) -> (isPure : Bool) -> (s : String) -> (fun : FunSig) ->
         (ctx : NamedCtxt) ->
         (0 _ : LanguageToCondition ctx.language fun isInfix isPure) =>
         (0 _ : NameIsNew ctx.language ctx.functions ctx.variables ctx.fvNames s) =>
         NamedCtxt
AddFun isInfix isPure s fun $ MkNamedCtxt language funs vars names = MkNamedCtxt language (funs:<fun) vars $ NewFun @{names} {isInfix} {isPure} {fun} s

public export %inline
(>>) : {0 arg : NamedCtxt -> Type} -> {0 arg' : NamedCtxt -> Type} -> 
       ((ctx : NamedCtxt) -> (0 _ : arg ctx) => (0 _ : arg' ctx) => NamedCtxt) -> 
       (ctx : NamedCtxt) -> (0 _ : arg ctx) => (0 _ : arg' ctx) => NamedCtxt
(>>) f x = f x

public export %inline
Enough : SupportedLanguages -> NamedCtxt
Enough l = MkNamedCtxt l [<] [<] Empty

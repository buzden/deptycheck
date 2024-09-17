module Language.PilFun.Pretty.DSL

import public Data.So

import public Language.PilFun.Pretty

%default total

public export
record NamedCtxt where
  constructor MkNamedCtxt
  functions : Funs
  variables : Vars
  fvNames   : UniqNames functions variables

public export %inline
AddFun : (isInfix : Bool) -> (s : String) -> (fun : FunSig) ->
         (0 _ : So $ not isInfix || fun.From.length >= 1) =>
         (ctx : NamedCtxt) ->
         (0 _ : NameIsNew ctx.fvNames s) =>
         NamedCtxt
AddFun isInfix s fun $ MkNamedCtxt funs vars names = MkNamedCtxt (funs:<fun) vars $ NewFun @{names} {isInfix} {fun} s

public export %inline
(>>) : {0 arg : NamedCtxt -> Type} -> ((ctx : NamedCtxt) -> (0 _ : arg ctx) => NamedCtxt) -> (ctx : NamedCtxt) -> (0 _ : arg ctx) => NamedCtxt
(>>) f x = f x

public export %inline
Enough : NamedCtxt
Enough = MkNamedCtxt [<] [<] Empty

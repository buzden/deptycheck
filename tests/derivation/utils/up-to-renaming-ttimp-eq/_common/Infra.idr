module Infra

import public Deriving.DepTyCheck.Util.Reflection

import public Language.Reflection.Syntax

%default total

public export
interface GivesTTImp t where
  toTTImp : t -> Elab TTImp

export
GivesTTImp TTImp where
  toTTImp = pure

public export
NotTTImp : {k : _} -> (a : k) -> Bool
NotTTImp TTImp = False
NotTTImp _     = True

export
So (NotTTImp a) => GivesTTImp a where
  toTTImp x = quote x

export
checkEq : GivesTTImp expr1 => GivesTTImp expr2 => String -> Bool -> expr1 -> expr2 -> Elab Unit
checkEq desc res e1 e2 = do
  e1 <- toTTImp e1
  e2 <- toTTImp e2
  let ch1 : String -> TTImp -> TTImp -> Elab Unit
      ch1 desc l r = do
        logMsg "deptycheck.reflection.ttimp-eq-up-to-renamings" 0 $ if (l == r) @{UpToRenaming} == res
          then "\{desc}: OKAY"
          else """
               \{desc}: FAILED
                 - expr1: \{e1}
                 - expr2: \{e2}
                 - should equal: \{show res}
               """

      ch : String -> TTImp -> TTImp -> Elab Unit
      ch addDesc l r = do
        ch1 "\{desc} (\{addDesc}) >>" l r
        ch1 "\{desc} (\{addDesc}) <<" r l

  ch "plain" e1 e2
  ch "ap z" (e2 .$ `(Z)) (e1 .$ `(Z))
  ch "ap cross" (e2 .$ e1) (e1 .$ e2)
  ch "wrap case" (wrapCase e1) (wrapCase e2)

  where
    wrapCase : TTImp -> TTImp
    wrapCase e = ICase EmptyFC [] `(2 + zz) `(Prelude.Some.Typ) [cs `{x}, cs `{z}] where
      cs : Name -> Clause
      cs n = PatClause EmptyFC (var n) e

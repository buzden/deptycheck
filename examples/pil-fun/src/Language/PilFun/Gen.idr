module Language.PilFun.Gen

import Language.PilFun

import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 5

%hint
UsedConstructorDerivator : ConstructorDerivator
UsedConstructorDerivator = LeastEffort {simplificationHack = True}

export
genStmts : Fuel -> (funs : Funs) -> (preVars : Vars) -> Gen MaybeEmpty (postVars ** Stmts funs preVars postVars)
genStmts = deriveGen

module Language.PilFun.Gen

import Language.PilFun

import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 5

%hint
UsedConstructorDerivator : ConstructorDerivator
UsedConstructorDerivator = LeastEffort {simplificationHack = True}

export
genStmts : Fuel -> (funs : Funs) -> (vars : Vars) -> (mfd : Nat) -> (retTy : MaybeTy) -> Gen MaybeEmpty $ Stmts funs vars mfd retTy
genStmts = deriveGen

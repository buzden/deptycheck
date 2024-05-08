module Language.PilFun.Derived

import public Language.PilFun

import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 5

%hint LE : ConstructorDerivator; LE = LeastEffort {simplificationHack = True}

Language.PilFun.genStmts = deriveGen

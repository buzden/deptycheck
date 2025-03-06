module Language.PilFun.Derived

import public Language.PilFun

import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 5
%logging "deptycheck.derive.least-effort" 7

Language.PilFun.genStmts = deriveGen

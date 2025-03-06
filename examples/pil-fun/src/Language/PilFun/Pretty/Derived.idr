module Language.PilFun.Pretty.Derived

import public Language.PilFun.Pretty

import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 5
%logging "deptycheck.derive.least-effort" 7

Language.PilFun.Pretty.rawNewName = deriveGen

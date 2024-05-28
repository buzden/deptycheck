module Language.PilFun.Pretty.Derived

import public Language.PilFun.Pretty

import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 5

%hint LE : ConstructorDerivator; LE = LeastEffort {simplificationHack = True}

Language.PilFun.Pretty.genNewName = deriveGen

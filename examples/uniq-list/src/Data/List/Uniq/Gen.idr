module Data.List.Uniq.Gen

import public Data.List.Uniq

import public Test.DepTyCheck.Gen
import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 5

%hint
UsedConstructorDerivator : ConstructorDerivator
UsedConstructorDerivator = LeastEffort {simplificationHack = True}

Data.List.Uniq.genUniqStrList = deriveGen

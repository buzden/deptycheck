module Data.List.Uniq.Gen

import public Data.List.Uniq

import public Test.DepTyCheck.Gen
import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 5
%logging "deptycheck.derive.least-effort" 7

Data.List.Uniq.genUniqStrList = deriveGen

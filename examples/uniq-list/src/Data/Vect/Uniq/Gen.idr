module Data.Vect.Uniq.Gen

import public Data.Vect.Uniq

import public Test.DepTyCheck.Gen
import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 5

Data.Vect.Uniq.genUniqStrVect = deriveGen

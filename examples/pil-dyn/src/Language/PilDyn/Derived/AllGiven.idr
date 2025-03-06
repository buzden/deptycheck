module Language.PilDyn.Derived.AllGiven

import public Language.PilDyn
import public Language.PilDyn.Utils

import public Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive.least-effort" 7

export
genLinBlock__ : Fuel -> (Fuel -> Gen MaybeEmpty Int32) => {r : _} -> (ins, outs : Regs r) -> Gen MaybeEmpty $ LinBlock ins outs
genLinBlock__ = deriveGen

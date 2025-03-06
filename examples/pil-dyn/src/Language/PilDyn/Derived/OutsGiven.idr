module Language.PilDyn.Derived.OutsGiven

import public Language.PilDyn
import public Language.PilDyn.Utils

import public Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive.least-effort" 7

export
genLinBlock'_ : Fuel -> (Fuel -> Gen MaybeEmpty Int32) => {r : _} -> (outs : Regs r) -> Gen MaybeEmpty (ins : Regs r ** LinBlock ins outs)
genLinBlock'_ = deriveGen

module Language.PilDyn.Derived.OutsGiven

import public Language.PilDyn
import public Language.PilDyn.Utils

import public Deriving.DepTyCheck.Gen

%default total

export
genLinBlock'_ : Fuel -> (Fuel -> Gen MaybeEmpty Int32) => {r : _} -> (outs : Regs r) -> Gen MaybeEmpty (ins : Regs r ** LinBlock ins outs)
genLinBlock'_ = deriveGen

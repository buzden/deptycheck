module Language.PilDyn.Derived.InsGiven

import public Language.PilDyn
import public Language.PilDyn.Utils

import public Deriving.DepTyCheck.Gen

%default total

export
genLinBlock_' : Fuel -> (Fuel -> Gen MaybeEmpty Int32) => {r : _} -> (ins : Regs r) -> Gen MaybeEmpty (outs : Regs r ** LinBlock ins outs)
genLinBlock_' = deriveGen

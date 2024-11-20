module Language.PilDyn.Derived.NoGiven

import public Language.PilDyn
import public Language.PilDyn.Utils

import public Deriving.DepTyCheck.Gen

%default total

export
genLinBlock'' : Fuel -> (Fuel -> Gen MaybeEmpty Int32) => (r : _) -> Gen MaybeEmpty (ins : Regs r ** outs : Regs r ** LinBlock ins outs)
genLinBlock'' = deriveGen

module Data.List.Covering.Gen

import public Data.List.Covering

import public Test.DepTyCheck.Gen
import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 5

export
genCoveringSequence : Fuel -> {n : Nat} -> (bs : BitMask n) -> Gen MaybeEmpty $ CoveringSequence n bs
genCoveringSequence = deriveGen

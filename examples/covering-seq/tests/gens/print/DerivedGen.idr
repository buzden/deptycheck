module DerivedGen

import Data.List.Covering

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter $ Fuel -> {n : Nat} -> (bs : BitMask n) -> Gen MaybeEmpty $ CoveringSequence n bs

module DerivedGen

import PrintDerivation

import Data.List.Covering

%default total

%language ElabReflection

%runElab printDerived $ Fuel -> {n : Nat} -> (bs : BitMask n) -> Gen MaybeEmpty $ CoveringSequence n bs

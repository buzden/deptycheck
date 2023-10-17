module DerivedGen

import AlternativeCore
import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> Gen MaybeEmpty Nat
checkedGen = deriveGen {core=CallSelf}

main : IO Unit
main = runGs [ G checkedGen ]

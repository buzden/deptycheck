module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

-- `a` is placed *before* the fuel parameter, which is unsupported
checkedGen : {a : Type} -> Fuel -> Gen $ Maybe a
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen {a=Nat} fl ]

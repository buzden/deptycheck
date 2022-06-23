module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data EqA : (a : Type) -> a -> Type where
  MkEqA : {x : b} -> (x = x) -> EqA b x

Show (EqA a x) where
  show _ = "Refl"

genBool : Fuel -> Gen Bool
genBool = deriveGen

checkedGen : Fuel -> {a : Type} -> (x : a) -> (Fuel -> Gen a) => Gen (EqA a x)
checkedGen = deriveGen

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl (the Nat 0) @{smallNats}
  , G $ \fl => checkedGen fl (the Nat 4) @{smallNats}
  , G $ \fl => checkedGen fl (the Nat 4) @{smallNats}
  , G $ \fl => checkedGen fl False @{genBool}
  , G $ \fl => checkedGen fl False @{genBool}
  , G $ \fl => checkedGen fl ""   @{smallStrs}
  , G $ \fl => checkedGen fl "ab" @{smallStrs}
  , G $ \fl => checkedGen fl "ab" @{smallStrs}
  ]

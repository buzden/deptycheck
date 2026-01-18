module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data Y : Nat -> Type where
  MkY : Vect n (Fin n) -> Y n

data X = MkX (Y 3)

%hint
YShow : Show (Y n)
YShow = %runElab derive

%hint
XShow : Show X
XShow = %runElab derive

export
checkedGen : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty X
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{smallNats} ]

module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

Show (x ** Gen MaybeEmpty x) where
  show _ = "a generator"

checkedGen : Fuel -> (em : _) -> Gen MaybeEmpty (a ** Gen em a)
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl MaybeEmpty ]

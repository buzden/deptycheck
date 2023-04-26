module DerivedGen

import public RunDerivedGen

%default total

%language ElabReflection

data X = MkX (Gen MaybeEmpty Bool)

Show X where
  show _ = #"an "X""#

gensGen : Fuel -> (em : Emptiness) -> (a : Type) -> Gen MaybeEmpty $ Gen em a
gensGen _ em Bool = elements $ pure <$> [True, False]
gensGen _ em Nat  = elements $ pure <$> fromList [0 .. 99]
gensGen _ _  _    = empty

-- Check that demanding the gen of gens is allowed and is used
checkedGen : Fuel -> (Fuel -> (em : Emptiness) -> (a : Type) -> Gen MaybeEmpty $ Gen em a) => Gen MaybeEmpty X
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{gensGen} ]

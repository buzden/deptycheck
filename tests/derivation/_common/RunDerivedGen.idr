module RunDerivedGen

import public Deriving.DepTyCheck.Gen

import public Generics.Derive

import System.Random.Pure.StdGen

%default total

export %hint
smallStrs : Fuel -> Gen MaybeEmpty String
smallStrs _ = elements ["", "a", "bc"]

export %hint
smallNats : Fuel -> Gen MaybeEmpty Nat
smallNats _ = elements [0, 10]

export
aVect : Fuel -> (Fuel -> Gen MaybeEmpty a) => (n : Nat) -> Gen MaybeEmpty (Vect n a)
aVect f Z             = [| [] |]
aVect f (S n) @{genA} = [| genA f :: aVect f n @{genA} |]

export %hint
someTypes : Fuel -> Gen MaybeEmpty Type
someTypes _ = elements [Nat, String, Bool]

export
Show (a = b) where
  show Refl = "Refl"

public export
data GenForRun : Type where
  G : Show x => (Fuel -> Gen MaybeEmpty x) -> GenForRun

export
runGs : List GenForRun -> IO Unit
runGs checkedGens = do
  putStrLn "Generated values:"
  let genedValues = checkedGens <&> \(G gen) => map show $ unGenTryN 10 someStdGen $ gen $ limit 20
  let delim = (putStrLn "-----" >>)
  for_ genedValues $ delim . Lazy.traverse_ (delim . putStrLn)

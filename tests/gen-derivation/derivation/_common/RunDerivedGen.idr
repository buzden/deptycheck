module RunDerivedGen

import public Deriving.DepTyCheck.Gen

import public Generics.Derive

import System.Random.Pure.StdGen

%default total

export
smallStrs : Fuel -> Gen String
smallStrs _ = elements ["", "a", "bc"]

export
smallNats : Fuel -> Gen Nat
smallNats _ = elements [0, 10]

export
aVect : Fuel -> (Fuel -> Gen a) => (n : Nat) -> Gen (Vect n a)
aVect f Z             = [| [] |]
aVect f (S n) @{genA} = [| genA f :: aVect f n @{genA} |]

export
someTypes : Fuel -> Gen Type
someTypes _ = elements [Nat, String, Bool]

namespace SomeTestType

  public export -- it would be good if this worked for non-public too
  data SomeTestType : (n : Nat) -> Type where
    MkSomeTestType : String -> Vect n Nat -> SomeTestType n

  export
  Show (SomeTestType n) where
    show (MkSomeTestType desc xs) = "MkSomeTestType \{show desc} \{show xs}"

  export
  TunableSomeTestTypeGen : String -> Fuel -> (n : Nat) -> Gen $ SomeTestType n
  TunableSomeTestTypeGen desc f n = MkSomeTestType desc <$> aVect f @{smallNats} n

  export %hint
  HintedSomeTestTypeGen : Fuel -> (n : Nat) -> Gen $ SomeTestType n
  HintedSomeTestTypeGen = TunableSomeTestTypeGen "very-external"

export
Show (a = b) where
  show Refl = "Refl"

public export
data GenForRun : Type where
  G : Show x => (Fuel -> Gen x) -> GenForRun

export
runGs : List GenForRun -> IO Unit
runGs checkedGens = do
  putStrLn "Generated values:"
  let genedValues = checkedGens <&> \(G gen) => map show $ unGenTryN 10 someStdGen $ gen $ limit 20
  let delim = (putStrLn "-----" >>)
  for_ genedValues $ delim . Lazy.traverse_ (delim . putStrLn)

export %hint
UsedConstructorDerivator : ConstructorDerivator
UsedConstructorDerivator = LeastEffort

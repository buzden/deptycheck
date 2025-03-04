module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

import Data.Vect

%default total

%language ElabReflection

data IsFS : (n : _) -> Fin n -> Type where
  ItIsFS : IsFS _ (FS i)

%runElab deriveGenPrinter @{EmptyCons} $
  Fuel -> {n : Nat} -> (v : Fin n) -> Gen MaybeEmpty $ IsFS n v

module DerivedGen

import Data.So

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data BoolP : Unit -> Type where
  TrueP : BoolP x
  FalseP : BoolP x

f : BoolP x -> Bool
f TrueP = True
f FalseP = False

data X : Type where
  MkX : (u : Unit) -> (x : BoolP u) -> So (f x) -> X

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X

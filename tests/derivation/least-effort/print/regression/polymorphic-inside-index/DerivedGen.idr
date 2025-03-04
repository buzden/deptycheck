module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data Y : Maybe Unit -> Type where
  MkY : Y $ Just x

%runElab deriveGenPrinter $ Fuel -> (c : _) -> Gen MaybeEmpty $ Y c

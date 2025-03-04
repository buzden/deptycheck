module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data EqualN : Nat -> Nat -> Type where
  ReflN : EqualN x x

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (a ** b ** EqualN a b)

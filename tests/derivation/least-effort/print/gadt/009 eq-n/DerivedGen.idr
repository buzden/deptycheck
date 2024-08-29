module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data EqualN : Nat -> Nat -> Type where
  ReflN : EqualN x x

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (b : Nat) -> Gen MaybeEmpty (a ** EqualN a b)

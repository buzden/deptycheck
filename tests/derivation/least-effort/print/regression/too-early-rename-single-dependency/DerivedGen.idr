module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : Type where
  MkX : Nat -> Bool -> X

data Y : X -> Type where
  MkY : Y (MkX n b)

data Z : Type where
  MkZ : (x : X) ->
        Y x =>
        Z

data W : Z -> Z -> Type where
  MkW : W (MkZ (MkX n False)) (MkZ (MkX n True))

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (a : Z) -> (b : Z) -> Gen MaybeEmpty (W a b)

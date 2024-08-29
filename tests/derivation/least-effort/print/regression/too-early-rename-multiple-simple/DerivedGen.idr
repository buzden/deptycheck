module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : Type where
  MkX : Nat -> Nat -> Bool -> X

data Y : X -> Type where
  MkY : Y (MkX n m b)

data Z : Type where
  MkZ : (x : X) ->
        Y x =>
        Z

data W : Z -> Z -> Type where
  MkW : W (MkZ (MkX n m False)) (MkZ (MkX n m True))

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (a : Z) -> (b : Z) -> Gen MaybeEmpty (W a b)

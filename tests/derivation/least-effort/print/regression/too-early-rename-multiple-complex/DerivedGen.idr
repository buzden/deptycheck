module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : Type where
  MkX : Nat -> Bool -> X

data Y : X -> X -> Type where
  MkY : Y (MkX n b) (MkX m b)

data Z : Type where
  MkZ : (x : X) ->
        (x' : X) ->
        Y x x' =>
        Z

data W : Z -> Z -> Type where
  MkW : W (MkZ (MkX n False) (MkX m False)) (MkZ (MkX n True) (MkX m True))

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (a : Z) -> (b : Z) -> Gen MaybeEmpty (W a b)

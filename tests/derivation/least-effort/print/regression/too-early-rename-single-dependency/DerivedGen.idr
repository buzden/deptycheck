module DerivedGen

import AlternativeCore
import PrintDerivation

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

%runElab printDerived @{LeastEffort} $ Fuel -> (a : Z) -> (b : Z) -> Gen MaybeEmpty (W a b)

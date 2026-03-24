module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Vect

%language ElabReflection

record C where
  constructor Mk
  len : Nat

data Each : {arity : _} -> (m : C) -> (vals : Vect arity (Fin m.len)) -> Type where
  Next : {m : C} -> {0 vals : Vect n _} -> {0 val : _} -> Each m (val :: vals)

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> {arity : _} -> (m : C) -> (vals : Vect arity (Fin m.len)) -> Gen MaybeEmpty (Each m vals)

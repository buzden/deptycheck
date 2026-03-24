module DerivedGen

import RunDerivedGen

import Data.Vect

record C where
  constructor Mk
  len : Nat

data Each : {arity : _} -> (m : C) -> (vals : Vect arity (Fin m.len)) -> Type where
  Next : {m : C} -> {0 vals : Vect n _} -> {0 val : _} -> Each m (val :: vals)

checkedGen : Fuel -> {arity : _} -> (m : C) -> (vals : Vect arity (Fin m.len)) -> Gen MaybeEmpty (Each m vals)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

{vs : _} -> Show (Each m vs) where
  show (Next {m=Mk l}) = "Next : Each (Mk \{show l}) \{show vs}"

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl (Mk 5) [0, 1, 3]
  ]

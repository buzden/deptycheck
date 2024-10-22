module DerivedGen

import RunDerivedGen

import Data.So

%default total

%language ElabReflection

record R where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
  f : Nat
  {auto cd : So $ c == d}
  {auto be : So $ b == e}
  {auto af : So $ a == f}
  {auto ab : So $ a == b}

Show R where
  show r = "(\{show r.a}, \{show r.b}, \{show r.c}, \{show r.d}, \{show r.e}, \{show r.f})"

checkedGen : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

%hint
usedNatGen : Gen0 Nat
usedNatGen = elements [0 .. 99]

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]

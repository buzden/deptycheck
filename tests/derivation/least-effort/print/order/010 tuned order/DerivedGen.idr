module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : Nat -> Type where
  MkX : (x : Nat) -> X x

namespace Hide

  export
  unX : X n -> Nat
  unX $ MkX x = x

data Y : Nat -> Type where
  MkYSimple : (bef : Nat) -> (a : X $ n + 2) -> (aft : Nat) -> Y n -- `bef` and `aft` must go after `a` and needed for it `n`
  MkYComplex : (bef : Nat) -> (v : Fin $ unX x) -> (a : X $ finToNat v) -> (aft : Nat) -> Y n -- `bef`, `aft` and `n` must go after `a` + needed rest

GenOrderTuning `{MkYSimple}.dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [`{a}]

GenOrderTuning `{MkYComplex}.dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [`{a}]

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (n ** Y n)

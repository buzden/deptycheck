module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data Duplicate : (dst : Fin n) -> (src : Fin n) -> (vs : Fin n) -> Fin n -> Type where
  JustDup : Duplicate {n=S n} dst src vs FZ

record Context (n : Nat) where
  constructor Ctx

  openLoops : Fin n
  undeterminedCount : Nat
  registers : Fin n
  freeSources : Fin n

data Program : (ctx : Context n) -> Type where
  Assign : (target : Fin n) -> (i : Fin n) ->
           Duplicate target i regs contRegs =>
           Program {n} (Ctx ols uc contRegs fs) ->
           Program {n} $ Ctx ols uc regs fs
  Finish : Program ctx

%language ElabReflection
%logging "deptycheck.derive.least-effort" 7

checkedGen : Fuel -> (n : Nat) -> (ctx : Context n) -> Gen MaybeEmpty (Program ctx)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

Show (Program ctx) where
  show Finish = "stop"
  show (Assign t i cont) = "\{show t} := \{show i}; \{show cont}"

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 5 $ Ctx 3 15 4 3
  , G $ \fl => checkedGen fl 100 $ Ctx 30 15 40 30
  ]

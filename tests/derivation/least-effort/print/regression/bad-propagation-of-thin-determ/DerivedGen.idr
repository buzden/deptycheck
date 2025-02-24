module DerivedGen

import Deriving.DepTyCheck.Gen

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

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (n : Nat) -> (ctx : Context n) -> Gen MaybeEmpty (Program ctx)

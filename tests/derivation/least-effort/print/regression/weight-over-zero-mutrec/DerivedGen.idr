module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data Basic = LL | WW

data Ty : Type
data ArrTy : Ty -> Nat -> Nat -> Type
data CanBeInPArr : Ty -> Type

data Ty = Arr (ArrTy t s e) | Var Basic

data ArrTy : Ty -> Nat -> Nat -> Type where
  Unp : (t : Ty) -> (start : Nat) -> (end : Nat) -> ArrTy t start end
  Pck : (t : Ty) -> (start : Nat) -> (end : Nat) -> CanBeInPArr t => ArrTy t start end

data CanBeInPArr : Ty -> Type where
  L : CanBeInPArr (Var LL)
  P : CanBeInPArr (Arr (Pck {} @{_}))

data EqSuperBasic : Ty -> Ty -> Type where
  EqBasicV :                      EqSuperBasic (Var t)               (Var t')
  EqBasicP : EqSuperBasic t t' -> EqSuperBasic (Arr $ Pck t {} @{_}) (Arr $ Pck t' {} @{_})
  EqBasicU : EqSuperBasic t t' -> EqSuperBasic (Arr $ Unp t {})      (Arr $ Unp t' {})

%language ElabReflection

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (a, b : _) -> Gen MaybeEmpty $ EqSuperBasic a b

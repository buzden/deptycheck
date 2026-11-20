module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data Ty = NatTy | VecTy Nat Ty

data X : Ty -> Type where
  VNat  : Nat -> X NatTy
  VNil  : X (VecTy 0 a)
  VCons : X a -> X (VecTy n a) -> X (VecTy (S n) a)

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (t : Ty) -> Gen MaybeEmpty (X t)

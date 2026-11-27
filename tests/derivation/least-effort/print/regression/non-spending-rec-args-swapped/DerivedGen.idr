module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data Ty = Base | Arr Ty Ty

data X : Ty -> Ty -> Type where
  SBase : X Base Base
  SArr  : X c a -> X b d -> X (Arr a b) (Arr c d)

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (a, b : Ty) -> Gen MaybeEmpty (X a b)

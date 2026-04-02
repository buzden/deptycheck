module Test

import Shared

%default total

%language ElabReflection

data Y : Type -> Type where
  MkY : Either Nat a -> Y a

%runElab specialiseDataLam' "EitherSpec" $ \a, b => Either Nat (Y (Either (Fin a) b))

%runElab specialiseDataLam' "EitherSpec2" $ \a, b => EitherSpec a b

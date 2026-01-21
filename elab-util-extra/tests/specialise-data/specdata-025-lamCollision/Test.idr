module Test

import Shared

%default total

%language ElabReflection
%logging "specialiseData" 20
%logging "specialiseData.specDecls" 0

data Y : Type -> Type where
  MkY : Either Nat a -> Y a

data X : Type where
  MkX : Either Nat (Y $ Either (Fin 5) String) -> X

Show a => Show (Y a) where
  showPrec d $ MkY e = showCon d "MkY" $ showArg e

Show X where
  showPrec d $ MkX xs = showCon d "MkX" $ showArg xs

%runElab specialiseDataLam' "EitherSpec" $ \a, b => Either Nat (Y (Either (Fin a) b))

%runElab specialiseDataLam' "EitherSpec2" $ \a, b => EitherSpec a b


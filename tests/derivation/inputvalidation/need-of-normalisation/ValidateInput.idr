module ValidateInput

import Deriving.DepTyCheck.Gen

%default total

data X = MkX

data X' = MkX'

data Y : Type -> Type -> Type where
  MkY : Y Int String

genY_0 : Fuel -> (a, b : Type) -> Gen0 $ Y a b
genY_0 = deriveGen

GenF : Type
GenF = (a, b : Type) -> Gen0 $ Y a b

genY_genF : Fuel -> GenF
genY_genF = deriveGen

PartGenF : Type -> Type
PartGenF a = (b : Type) -> Gen0 $ Y a b

genY_partGenF : Fuel -> (a : _) -> PartGenF a
genY_partGenF = deriveGen

Z : Type -> Type -> Type
Z x = Y x

genZ : (a, b : _) -> Gen0 $ Z a b

ErsatzTy : Type
ErsatzTy = Type

genZ_ersatz : Fuel -> (a : Type) -> (b : ErsatzTy) -> Gen0 $ Z a b
genZ_ersatz = deriveGen

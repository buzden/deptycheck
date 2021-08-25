||| Internal generation functions, after user input checks
module Test.DepTyCheck.Gen.Auto.Checked

import public Language.Reflection.Types

import public Test.DepTyCheck.Gen.Auto.Util

%default total

-----------------------------------------------------
--- Data types for the safe signature formulation ---
-----------------------------------------------------

public export
data ArgExplicitness = ExplicitArg | ImplicitArg

public export
Eq ArgExplicitness where
  ExplicitArg == ExplicitArg = True
  ImplicitArg == ImplicitArg = True
  _ == _ = False

--- Datatype that describes one particular generator ---

public export
record GenSignature f where
  constructor MkGenSignature
  targetType : TypeInfo

  -- non-checked, but meant to be that these two do not intersect and their union is a full set
  paramsToBeGenerated : f $ Fin targetType.args.length
  givenParams         : f $ Fin targetType.args.length

public export
Foldable f => Eq (GenSignature f) where
  MkGenSignature ty1 gen1 giv1 == MkGenSignature ty2 gen2 giv2
    = ty1.name == ty2.name && (gen1 `equiv` gen2) && (giv1 `equiv` giv2)
    where
      equiv : forall n, m. f (Fin n) -> f (Fin m) -> Bool
      equiv f1 f2 = (finToNat <$> toList f1) == (finToNat <$> toList f2)

namespace GenSignature

  public export
  mapCarrier : (forall a. f a -> g a) -> GenSignature f -> GenSignature g
  mapCarrier h (MkGenSignature ty gen giv) = MkGenSignature ty .| h gen .| h giv

--- Info of external generators ---

public export
record GenExternals f where
  constructor MkGenExternals
  autoImplExternals : f $ GenSignature f
  hintedExternals   : f $ GenSignature f

namespace GenExternals

  public export
  mapCarrier : Functor f => (forall a. f a -> g a) -> GenExternals f -> GenExternals g
  mapCarrier h (MkGenExternals ae he) = MkGenExternals .| h (mapCarrier h <$> ae) .| h (mapCarrier h <$> he)

------------------------------------------
--- The entry-point generator function ---
------------------------------------------

||| Internal generation functions, after user input checks
module Test.DepTyCheck.Gen.Auto.Checked

import public Control.Monad.Reader
import public Control.Monad.Trans
import public Control.Monad.Writer

import public Data.SortedMap
import public Data.SortedSet

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

public export
Foldable f => Ord (GenSignature f) where
  compare = comparing $ \(MkGenSignature ty gen giv) => (show ty.name, finToNat <$> toList gen, finToNat <$> toList giv)

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

-----------------------------------
--- "Canonical" functions stuff ---
-----------------------------------

--- Main interfaces ---

public export %inline
GenSigS : Type
GenSigS = GenSignature SortedSet

public export
interface Monad m => CanonicName m where
  canonicName : GenSigS -> m Name

--- Signature-of-list functions ---

export
externalLambda : CanonicName m => GenSignature List -> m TTImp
externalLambda sig = do
  ?foo_ext_lambda -- a remapping between a lambda from external signature and a function from canonical one

export
wrapExternals : CanonicName m => GenExternals List -> (lambda : TTImp) -> m TTImp
wrapExternals exts lambda = do
  ?wrapExternals_rhs

--- Signature-of-set functions --

canonicSig : GenSigS -> TTImp
canonicSig sig = ?canonicSig_rhs

export
deriveCanonical : CanonicName m => GenSigS -> m Decl
deriveCanonical sig = do
  ?deriveCanonical_rhs

--- Implementations for the canonic interfaces ---

MonadReader (SortedMap GenSigS Name) m =>
MonadWriter (SortedMap GenSigS $ Lazy Decl) m =>
CanonicName m where
  canonicName sig = do
    let Nothing = lookup sig !ask
      | Just n => pure n
    tell $ singleton sig $ delay !(deriveCanonical sig) -- looks like `deriveCanonical` is called not in a lazy way
    pure $ MN "\{show sig.targetType.name} given \{show sig.givenParams}" 0

--- Canonic-dischagring function ---

export
runCanonic : GenExternals List -> (forall m. CanonicName m => m a) -> Elab (a, List Decl)
runCanonic exts calc = ?runCanonic_rhs

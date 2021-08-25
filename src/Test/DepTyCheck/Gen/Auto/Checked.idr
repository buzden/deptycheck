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

--- Datatypes to describe parsed user signatures ---

public export
record ParsedUserGenSignature where
  constructor MkParsedUserGenSignature
  targetType : TypeInfo

  -- non-checked, but meant to be that these two do not intersect and their union is a full set
  paramsToBeGenerated : List $ Fin targetType.args.length
  givenParams         : List $ Fin targetType.args.length

public export
Eq ParsedUserGenSignature where
  (==) = (==) `on` \(MkParsedUserGenSignature ty gen giv) => (ty.name, toNatList gen, toNatList giv)

public export
record ParsedUserGenExternals where
  constructor MkParsedUserGenExternals
  autoImplExternals : List ParsedUserGenSignature
  hintedExternals   : List ParsedUserGenSignature

--- Datatypes to describe derived canonic signatures ---

public export
record CanonicGenSignature where
  constructor MkCanonicGenSignature
  targetType : TypeInfo

  -- non-checked, but meant to be that these two do not intersect and their union is a full set
  paramsToBeGenerated : SortedSet $ Fin targetType.args.length
  givenParams         : SortedSet $ Fin targetType.args.length

namespace CanonicGenSignature

  characteristics : CanonicGenSignature -> (String, List Nat, List Nat)
  characteristics (MkCanonicGenSignature ty gen giv) = (show ty.name, toNatList gen, toNatList giv)

public export
Eq CanonicGenSignature where
  (==) = (==) `on` characteristics

public export
Ord CanonicGenSignature where
  compare = comparing characteristics

public export
record CanonicGenExternals where
  constructor MkCanonicGenExternals
  externals : SortedSet CanonicGenSignature

-----------------------------------
--- "Canonical" functions stuff ---
-----------------------------------

--- Main interfaces ---

public export
interface Monad m => CanonicName m where
  canonicName : CanonicGenSignature -> m Name

--- Signature-of-list functions ---

export
externalLambda : CanonicName m => ParsedUserGenSignature -> m TTImp
externalLambda sig = do
  ?foo_ext_lambda -- a remapping between a lambda from external signature and a function from canonical one

export
wrapExternals : CanonicName m => ParsedUserGenExternals -> (lambda : TTImp) -> m TTImp
wrapExternals exts lambda = do
  ?wrapExternals_rhs

--- Signature-of-set functions --

canonicSig : CanonicGenSignature -> TTImp
canonicSig sig = ?canonicSig_rhs

export
deriveCanonical : CanonicName m => CanonicGenSignature -> m Decl
deriveCanonical sig = do
  ?deriveCanonical_rhs

--- Implementations for the canonic interfaces ---

MonadReader (SortedMap CanonicGenSignature Name) m =>
MonadWriter (SortedMap CanonicGenSignature $ Lazy Decl) m =>
CanonicName m where
  canonicName sig = do
    let Nothing = lookup sig !ask
      | Just n => pure n
    tell $ singleton sig $ delay !(deriveCanonical sig) -- looks like `deriveCanonical` is called not in a lazy way
    pure $ MN "\{show sig.targetType.name} given \{show sig.givenParams}" 0

--- Canonic-dischagring function ---

export
runCanonic : ParsedUserGenExternals -> (forall m. CanonicName m => m a) -> Elab (a, List Decl)
runCanonic exts calc = ?runCanonic_rhs

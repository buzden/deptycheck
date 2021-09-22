||| Interfaces for using a derivator
module Test.DepTyCheck.Gen.Auto.Derive

import public Control.Monad.Error.Interface

import public Data.SortedMap
import public Data.SortedMap.Dependent
import public Data.SortedSet

import public Test.DepTyCheck.Gen.Auto.Util

%default total

---------------------------------------------------
--- Simplest `Gen` signature, user for requests ---
---------------------------------------------------

public export
record GenSignature where
  constructor MkGenSignature
  targetType : TypeInfo
  givenParams : SortedSet $ Fin targetType.args.length

namespace GenSignature

  export
  characteristics : GenSignature -> (String, List Nat)
  characteristics $ MkGenSignature ty giv = (show ty.name, toNatList giv)

public export
Eq GenSignature where
  (==) = (==) `on` characteristics

public export
Ord GenSignature where
  compare = comparing characteristics

----------------------
--- Main interface ---
----------------------

public export %inline
CanFailAtFC : (Type -> Type) -> Type
CanFailAtFC = MonadError (FC, String)

public export
interface Monad m => CanFailAtFC m => CanonicGen m where
  callGen : (sig : GenSignature) -> (fuel : TTImp) -> Vect sig.givenParams.asList.length TTImp -> m TTImp

export
failAt : CanonicGen m => FC -> String -> m a
failAt fc msg = throwError (fc, msg)

export
fail : CanonicGen m => String -> m a
fail = failAt EmptyFC

--- Low-level derivation interface ---

public export
interface DerivatorCore where
  internalGenSig  : GenSignature -> TTImp
  callInternalGen : (0 sig : GenSignature) -> (topmost : Name) -> (fuel : TTImp) -> Vect sig.givenParams.asList.length TTImp -> TTImp

  internalGenBody : CanonicGen m => GenSignature -> Name -> m $ List Clause

-- NOTE: Implementation of `internalGenBody` cannot know the `Name` of the called gen, thus it cannot use `callInternalGen` function directly.
--       It have to use `callGen` function from `CanonicGen` interface instead.
--       But `callInternalGen` function is still present here because, in some sense, it is a complementary to `internalGenSig`.
--       Internals and changes in the implementation of `internalGenSig` influence on the implementation of `callInternalGen`.

export
deriveCanonical : DerivatorCore => CanonicGen m => GenSignature -> Name -> m (Decl, Decl)
deriveCanonical sig name = pure (export' name (internalGenSig sig), def name !(internalGenBody sig name))

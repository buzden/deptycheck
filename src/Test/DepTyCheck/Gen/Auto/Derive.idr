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

public export
interface DerivatorCore where
  deriveCanonical : CanonicGen m => GenSignature -> Name -> m (Decl, Decl)

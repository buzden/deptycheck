module Test.DepTyCheck.Gen.Auto.Derive

import public Control.Monad.Error.Interface

import public Language.Reflection.Syntax
import public Language.Reflection.Types

import public Data.SortedMap
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

----------------------------
--- Derivation functions ---
----------------------------

-- Must respect names from the `givenParams` field, at least for implicit parameters
export
canonicSig : GenSignature -> TTImp
canonicSig sig = piAll returnTy $ MkArg MW ExplicitArg Nothing `(Data.Fuel.Fuel) :: (arg <$> SortedSet.toList sig.givenParams) where
  -- TODO Check that the resulting `TTImp` reifies to a `Type`? During this check, however, all types must be present in the caller's context.

  arg : Fin sig.targetType.args.length -> Arg False
  arg idx = let MkArg {name, type, _} = index' sig.targetType.args idx in MkArg MW ExplicitArg (Just name) type

  returnTy : TTImp
  returnTy = var `{Test.DepTyCheck.Gen.Gen} .$ buildDPair targetTypeApplied generatedArgs where

    targetTypeApplied : TTImp
    targetTypeApplied = foldr apply (var sig.targetType.name) $ reverse $ sig.targetType.args <&> \(MkArg {name, piInfo, _}) => case piInfo of
                          ExplicitArg   => (.$ var name)
                          ImplicitArg   => \f => namedApp f name $ var name
                          DefImplicit _ => \f => namedApp f name $ var name
                          AutoImplicit  => (`autoApp` var name)

    generatedArgs : List (Name, TTImp)
    generatedArgs = mapMaybeI' sig.targetType.args $ \idx, (MkArg {name, type, _}) =>
                      ifThenElse .| contains idx sig.givenParams .| Nothing .| Just (name, type)

-- Main meat function --

canonicBody : CanonicGen m => GenSignature -> m $ List Clause
canonicBody sig = do

  -- check that there is at least one constructor
  let (_::_) = sig.targetType.cons
    | [] => fail "No constructors found for the type `\{show sig.targetType.name}`"

  ?canonicBody_rhs

------------------------------
--- External user function ---
------------------------------

export
deriveCanonical : CanonicGen m => GenSignature -> Name -> m (Decl, Decl)
deriveCanonical sig name = pure (export' name (canonicSig sig), def name !(canonicBody sig))

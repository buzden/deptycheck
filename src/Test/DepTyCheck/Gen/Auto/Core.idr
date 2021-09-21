||| Main implementation of the derivator core interface
module Test.DepTyCheck.Gen.Auto.Core

import public Language.Reflection.Syntax
import public Language.Reflection.Types

import public Test.DepTyCheck.Gen.Auto.Derive

%default total

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
DerivatorCore where
  deriveCanonical sig name = pure (export' name (canonicSig sig), def name !(canonicBody sig))

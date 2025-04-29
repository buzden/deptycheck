||| Interfaces for using a one type derivator
module Deriving.DepTyCheck.Gen.InterfaceForOneType

import public Control.Monad.Error.Interface

import public Deriving.DepTyCheck.Gen.Signature

%default total

----------------------
--- Main interface ---
----------------------

public export
interface Elaboration m => NamesInfoInTypes => ConsRecs => CanonicGen m where
  needWeightFun : TypeInfo -> m ()
  callGen : (sig : GenSignature) -> (fuel : TTImp) -> Vect sig.givenParams.size TTImp -> m (TTImp, Maybe (gend ** Vect gend $ Fin gend))
  --                                                                                                     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  --                                                                   this is a permutation of generated arguments --/
  --                                                                   actually, `gend` can be calculated from `sig`, but we simplify things here

export
CanonicGen m => MonadTrans t => Monad (t m) => CanonicGen (t m) where
  needWeightFun = lift . needWeightFun
  callGen sig fuel params = lift $ callGen sig fuel params

--- Low-level derivation interface ---

export
canonicSig : GenSignature -> TTImp
canonicSig sig = piAll returnTy $ MkArg MW ExplicitArg Nothing `(Data.Fuel.Fuel) :: (arg <$> Prelude.toList sig.givenParams) where
  -- TODO Check that the resulting `TTImp` reifies to a `Type`? During this check, however, all types must be present in the caller's context.

  arg : Fin sig.targetType.args.length -> Arg
  arg idx = let MkArg {name, type, _} = index' sig.targetType.args idx in MkArg MW ExplicitArg name type

  returnTy : TTImp
  returnTy = `(Test.DepTyCheck.Gen.Gen Test.DepTyCheck.Gen.Emptiness.MaybeEmpty ~(buildDPair targetTypeApplied generatedArgs)) where

    targetTypeApplied : TTImp
    targetTypeApplied = foldr apply (extractTargetTyExpr sig.targetType) $ reverse $ sig.targetType.args <&> \(MkArg {name, piInfo, _}) => do
                          let name = stname name
                          case piInfo of
                            ExplicitArg   => (.$ var name)
                            ImplicitArg   => \f => namedApp f name $ var name
                            DefImplicit _ => \f => namedApp f name $ var name
                            AutoImplicit  => (`autoApp` var name)

    generatedArgs : List (Name, TTImp)
    generatedArgs = mapMaybeI sig.targetType.args $ \idx, (MkArg {name, type, _}) =>
                      ifThenElse .| contains idx sig.givenParams .| Nothing .| Just (stname name, type)

-- Complementary to `canonicSig`
export
callCanonic : (0 sig : GenSignature) -> (topmost : Name) -> (fuel : TTImp) -> Vect sig.givenParams.size TTImp -> TTImp
callCanonic _ = foldl app .: appFuel

public export
interface DerivatorCore where
  canonicBody : CanonicGen m => GenSignature -> Name -> m $ List Clause

-- NOTE: Implementation of `internalGenBody` cannot know the `Name` of the called gen, thus it cannot use `callCanonic` function directly.
--       It have to use `callGen` function from `CanonicGen` interface instead.
--       But `callCanonic` function is still present here because, in some sense, it is a complementary to `internalGenSig`.
--       Internals and changes in the implementation of `internalGenSig` influence on the implementation of `callCanonic`.

--- Expressions generation utils ---

defArgNames : {sig : GenSignature} -> Vect sig.givenParams.size Name
defArgNames = sig.givenParams.asVect <&> argName . index' sig.targetType.args

export %inline
canonicDefaultLHS' : (namesFun : Name -> String) -> GenSignature -> Name -> (fuel : String) -> TTImp
canonicDefaultLHS' nmf sig n fuel = callCanonic sig n .| bindVar fuel .| bindVar . nmf <$> defArgNames

export %inline
canonicDefaultRHS' : (namesFun : Name -> String) -> GenSignature -> Name -> (fuel : TTImp) -> TTImp
canonicDefaultRHS' nmf sig n fuel = callCanonic sig n fuel .| varStr . nmf <$> defArgNames

export %inline
canonicDefaultLHS : GenSignature -> Name -> (fuel : String) -> TTImp
canonicDefaultLHS = canonicDefaultLHS' show

export %inline
canonicDefaultRHS : GenSignature -> Name -> (fuel : TTImp) -> TTImp
canonicDefaultRHS = canonicDefaultRHS' show

---------------------------------
--- External-facing functions ---
---------------------------------

export
deriveCanonical : DerivatorCore => CanonicGen m => GenSignature -> Name -> m (Decl, Decl)
deriveCanonical sig name = pure (export' name (canonicSig sig), def name !(canonicBody sig name))

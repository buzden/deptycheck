module Test.DepTyCheck.Gen.Auto.Parsed

import public Test.DepTyCheck.Gen.Auto.Canonic

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
  givenParams         : List (ArgExplicitness, Fin targetType.args.length)

public export
Eq ParsedUserGenSignature where
  (==) = (==) `on` \(MkParsedUserGenSignature ty gen giv) => (ty.name, toNatList gen, toNatList $ snd <$> giv)

public export
record ParsedUserGenExternals where
  constructor MkParsedUserGenExternals
  autoImplExternals : List ParsedUserGenSignature
  hintedExternals   : List ParsedUserGenSignature

--- Parsed user's gen signature functions ---

export
externalLambda : CanonicName m => ParsedUserGenSignature -> m TTImp
externalLambda sig = do
  ?foo_ext_lambda -- a remapping between a lambda from external signature and a function from canonical one

export
wrapExternals : CanonicName m => ParsedUserGenExternals -> (lambda : TTImp) -> m TTImp
wrapExternals exts lambda = do
  ?wrapExternals_rhs

--- Canonic-dischagring function ---

export
runCanonic : ParsedUserGenExternals -> (forall m. CanonicName m => m a) -> Elab (a, List Decl)
runCanonic exts calc = ?runCanonic_rhs

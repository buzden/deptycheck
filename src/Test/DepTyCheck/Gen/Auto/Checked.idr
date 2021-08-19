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
record GenSignature where
  constructor MkGenSignature
  targetType : TypeInfo

  -- non-checked, but meant to be that these two do not intersect and their union is a full set
  paramsToBeGenerated : List $ Fin targetType.args.length
  givenParams         : List $ Fin targetType.args.length

public export
Eq GenSignature where
  MkGenSignature ty1 gen1 giv1 == MkGenSignature ty2 gen2 giv2
    = ty1.name == ty2.name && (finToNat <$> gen1) == (finToNat <$> gen2) && (finToNat <$> giv1) == (finToNat <$> giv2)

--- One particular generator + info of code position ---

public export
record GenSignatureWithFC where
  constructor MkGenSignatureWithFC
  sigFC        : FC
  genFC        : FC
  targetTypeFC : FC

  sigUnFC : GenSignature

public export
GenSignatureFC : Bool -> Type
GenSignatureFC False = GenSignature
GenSignatureFC True  = GenSignatureWithFC

--- One particular generator + info of external generators (+ possibly code position info) ---

public export
record GenInfraSignature withFC where
  constructor MkGenInfraSignature
  sig : GenSignatureFC withFC
  autoImplExternals : List $ GenSignatureFC withFC
  hintedExternals   : List $ GenSignatureFC withFC

public export
forgetFC : GenInfraSignature True -> GenInfraSignature False
forgetFC (MkGenInfraSignature sig autoImpls hinted) = MkGenInfraSignature sig.sigUnFC .| sigUnFC <$> autoImpls .| sigUnFC <$> hinted

------------------------------------------
--- The entry-point generator function ---
------------------------------------------

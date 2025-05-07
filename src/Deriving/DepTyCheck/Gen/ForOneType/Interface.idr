module Deriving.DepTyCheck.Gen.ForOneType.Interface

import public Deriving.DepTyCheck.Gen.ForAllNeededTypes.Interface
import public Deriving.DepTyCheck.Gen.Signature

%default total

------------------------------------------------------
--- Deriving body of a generator for a single type ---
------------------------------------------------------

public export
interface DeriveBodyForType where
  canonicBody : DerivationClosure m => GenSignature -> Name -> m $ List Clause

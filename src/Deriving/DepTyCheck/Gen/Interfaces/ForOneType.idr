module Deriving.DepTyCheck.Gen.Interfaces.ForOneType

import public Deriving.DepTyCheck.Gen.Interfaces.ForAllNeededTypes
import public Deriving.DepTyCheck.Gen.Signature

%default total

------------------------------------------------------
--- Deriving body of a generator for a single type ---
------------------------------------------------------

public export
interface DeriveBodyForType where
  canonicBody : DeriveClosure m => GenSignature -> Name -> m $ List Clause

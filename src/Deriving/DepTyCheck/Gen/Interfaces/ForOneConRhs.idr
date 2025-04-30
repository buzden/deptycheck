module Deriving.DepTyCheck.Gen.Interfaces.ForOneConRhs

import public Deriving.DepTyCheck.Gen.Interfaces.ForAllNeededTypes

%default total

------------------------------------------------------------
--- Derivation of a generator for constructor's body RHS ---
------------------------------------------------------------

--- Interface ---

public export
interface DeriveBodyRhsForCon where
  consGenExpr : DeriveClosure m => GenSignature -> (con : Con) -> (given : SortedSet $ Fin con.args.length) -> (fuel : TTImp) -> m TTImp

  ||| Workarond of inability to put an arbitrary name under `IBindVar`
  bindNameRenamer : Name -> String
  bindNameRenamer $ UN $ Basic n = n
  bindNameRenamer n = "^bnd^" ++ show n

module Deriving.DepTyCheck.Gen.ForOneTypeConRhs.Interface

import public Deriving.DepTyCheck.Gen.ForAllNeededTypes.Interface

%default total

------------------------------------------------------------
--- Derivation of a generator for constructor's body RHS ---
------------------------------------------------------------

--- Interface ---

public export
interface DeriveBodyRhsForCon where
  consGenExpr : DerivationClosure m => GenSignature -> (con : Con) -> (given : SortedSet $ Fin con.args.length) -> (fuel : TTImp) -> m TTImp

||| Workarond of inability to put an arbitrary name under `IBindVar`
export
bindNameRenamer : Name -> Name
bindNameRenamer n@(UN $ Basic _) = n
bindNameRenamer n = UN $ Basic $ "^bnd^" ++ show n

module Deriving.DepTyCheck.Gen.ForOneTypeConRhs.Interface

import public Deriving.DepTyCheck.Gen.ForAllNeededTypes.Interface

%default total

------------------------------------------------------------
--- Derivation of a generator for constructor's body RHS ---
------------------------------------------------------------

--- Interface ---

public export
interface DeriveBodyRhsForCon where
  consGenExpr : DerivationClosure m => Elaboration m => NamesInfoInTypes =>
                GenSignature -> (con : Con) -> (given : SortedSet $ Fin con.args.length) -> (fuel : TTImp) -> m TTImp

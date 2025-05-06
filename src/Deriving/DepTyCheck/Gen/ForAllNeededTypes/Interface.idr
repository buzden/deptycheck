module Deriving.DepTyCheck.Gen.ForAllNeededTypes.Interface

import public Deriving.DepTyCheck.Gen.ConsRecs
import public Deriving.DepTyCheck.Gen.Signature

%default total

--------------------------------------------------
--- Using and deriving of any needed generator ---
--------------------------------------------------

public export
interface Elaboration m => NamesInfoInTypes => ConsRecs => DeriveClosure m where
  needWeightFun : TypeInfo -> m ()
  callGen : (sig : GenSignature) -> (fuel : TTImp) -> Vect sig.givenParams.size TTImp -> m (TTImp, Maybe (gend ** Vect gend $ Fin gend))
  --                                                                                                     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  --                                                                   this is a permutation of generated arguments --/
  --                                                                   actually, `gend` can be calculated from `sig`, but we simplify things here

export
DeriveClosure m => MonadTrans t => Monad (t m) => DeriveClosure (t m) where
  needWeightFun = lift . needWeightFun
  callGen sig fuel params = lift $ callGen sig fuel params

-------------------
--- Conventions ---
-------------------

export
outmostFuelArg : Name
outmostFuelArg = UN $ Basic "^outmost-fuel^" -- I'm using a name containing chars that cannot be present in the code parsed from the Idris frontend

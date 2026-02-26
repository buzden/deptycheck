module Deriving.DepTyCheck.Gen.ForAllNeededTypes.Interface

import public Deriving.DepTyCheck.Gen.ConsRecs
import public Deriving.DepTyCheck.Gen.Signature

%default total

--------------------------------------------------
--- Using and deriving of any needed generator ---
--------------------------------------------------

public export
DerivationClosure : (Type -> Type) -> Type

export
needWeightFun : DerivationClosure m => NamesInfoInTypes => ConsRecs => TypeInfo -> m ()

export
callGen : DerivationClosure m => NamesInfoInTypes => ConsRecs =>
          (sig : GenSignature) -> (fuel : TTImp) -> Vect sig.givenParams.size TTImp -> m (TTImp, Maybe (gend ** Vect gend $ Fin gend))
--                                                                                                     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
--                                                                   this is a permutation of generated arguments --/
--                                                                   actually, `gend` can be calculated from `sig`, but we simplify things here

-------------------
--- Conventions ---
-------------------

export
outmostFuelArg : Name
outmostFuelArg = UN $ Basic "^outmost-fuel^" -- I'm using a name containing chars that cannot be present in the code parsed from the Idris frontend

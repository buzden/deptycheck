module Deriving.DepTyCheck.Gen.Interfaces.ForAllNeededTypes

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

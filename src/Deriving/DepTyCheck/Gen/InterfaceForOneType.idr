||| Interfaces for using a one type derivator
module Deriving.DepTyCheck.Gen.InterfaceForOneType

import public Control.Monad.Error.Interface

import public Deriving.DepTyCheck.Gen.Signature

%default total

----------------------
--- Main interface ---
----------------------

public export
interface Elaboration m => NamesInfoInTypes => ConsRecs => CanonicGen m where
  needWeightFun : TypeInfo -> m ()
  callGen : (sig : GenSignature) -> (fuel : TTImp) -> Vect sig.givenParams.size TTImp -> m (TTImp, Maybe (gend ** Vect gend $ Fin gend))
  --                                                                                                     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  --                                                                   this is a permutation of generated arguments --/
  --                                                                   actually, `gend` can be calculated from `sig`, but we simplify things here

export
CanonicGen m => MonadTrans t => Monad (t m) => CanonicGen (t m) where
  needWeightFun = lift . needWeightFun
  callGen sig fuel params = lift $ callGen sig fuel params

public export
interface DerivatorCore where
  canonicBody : CanonicGen m => GenSignature -> Name -> m $ List Clause

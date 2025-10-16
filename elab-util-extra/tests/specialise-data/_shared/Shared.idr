module Shared

import public Control.Monad.Either
import public Control.Monad.Writer
import public Control.Monad.Identity
import public Decidable.Decidable
import public Decidable.Equality
import public Data.DPair
import public Data.Vect
import public Data.SnocVect
import public Data.Vect.Quantifiers
import public Data.List
import public Data.List.Quantifiers
import public Derive.Prelude
import public Language.Reflection
import public Language.Reflection.Derive
import public Language.Reflection.Expr
import public Language.Reflection.Types
import public Language.Reflection.Types.Extra
import public Language.Reflection.Logging
import public Language.Reflection.Syntax
import public Language.Reflection.Syntax.Ops
import public Language.Reflection.Unify
import public Language.Reflection.VarSubst
import public Deriving.SpecialiseData
import public Data.Either
import public Data.SortedMap.Dependent

export
constructExprs : Type -> List TTImp -> Elab ()
constructExprs ty vals = do
  for_ vals $ \val => do
    c : ty <- check val
    pure ()

verifySingleCast : Type -> Type -> TTImp -> TTImp -> Elab ()
verifySingleCast a b a' b' = do
  aInst : a <- check a'
  bInst : b <- check b'
  aQuote <- quote aInst
  bQuote <- quote bInst
  castRes : b <- check `(cast ~aQuote)
  castRQuote <- quote castRes
  targ : Type <- check `(~bQuote = ~castRQuote)
  _ : targ <- check `(Refl)
  pure ()

verifyDoubleCast : Type -> Type -> TTImp -> Elab ()
verifyDoubleCast pt mt val = do
  val1 : mt <- check val
  val1' <- quote val1
  val2 : pt <- check `(cast ~val1')
  val2' <- quote val2
  val3 : mt <- check `(cast ~val2')
  val3' <- quote val3
  targ : Type <- check `(~val3' = ~val1')
  _ : targ <- check `(Refl)
  pure ()

export
verifySingleCasts' : Type -> Type -> List (TTImp, TTImp) -> Elab ()
verifySingleCasts' pt mt vals = do
  for_ vals $ \(val, val') => do
    verifySingleCast pt mt val val'
    verifySingleCast mt pt val' val

export
verifySingleCasts : Type -> Type -> List TTImp -> Elab ()
verifySingleCasts pt mt vals = verifySingleCasts' pt mt $ zip vals vals

export
verifyDoubleCasts : Type -> Type -> List TTImp -> Elab ()
verifyDoubleCasts pt mt vals = do
  for_ vals $ \val => do
    verifyDoubleCast pt mt val

verifyDecEq : Type -> Type -> TTImp -> TTImp -> Elab ()
verifyDecEq a b a' b' = do
  verA' : b <- check a'
  verB' : b <- check b'
  qA' <- quote verA'
  qB' <- quote verB'
  verA'' : a <- check `(cast ~qA')
  verB'' : a <- check `(cast ~qB')
  qA'' <- quote verA''
  qB'' <- quote verB''
  targ : Type <- check `(isYes (decEq ~qA' ~qB') = isYes (decEq ~qA'' ~qB''))
  _ : targ <- check `(Refl)
  pure ()

verifyEq : Type -> Type -> TTImp -> TTImp -> Elab ()
verifyEq a b a' b' = do
  verA' : b <- check a'
  verB' : b <- check b'
  qA' <- quote verA'
  qB' <- quote verB'
  verA'' : a <- check `(cast ~qA')
  verB'' : a <- check `(cast ~qB')
  qA'' <- quote verA''
  qB'' <- quote verB''
  targ : Type <- check `((~qA' == ~qB') = (~qA'' == ~qB''))
  _ : targ <- check `(Refl)
  targ' : Type <- check `((~qA' /= ~qB') = (~qA'' /= ~qB''))
  _ : targ' <- check `(Refl)
  pure ()

verifyShow : Type -> Type -> TTImp -> Elab ()
verifyShow a b a' = do
  verA' : b <- check a'
  qA' <- quote verA'
  verA'' : a <- check `(cast ~qA')
  qA'' <- quote verA''
  s1 : String <- check `(show ~qA')
  qS1 <- quote s1
  s2 : String <- check `(show ~qA'')
  qS2 <- quote s2
  showsAreEqual : Bool <- check `(~qS1 == ~qS2)
  if showsAreEqual
     then pure ()
     else do
       qB <- quote b
       failAt (getFC a') "Show implementation of type \{show qB} is wrong. When showing \{show qB}, expected \{s1}, but got \{s2}"

export
verifyShows : Type -> Type -> List TTImp -> Elab ()
verifyShows pt mt vals = do
  for_ vals $ \val => do
    verifyShow pt mt val

export
verifyDecEqs : Type -> Type -> List TTImp -> Elab ()
verifyDecEqs pt mt vals = do
  for_ (MkPair <$> vals <*> vals) $ \(val, val') => do
    verifyDecEq pt mt val val'

export
verifyEqs : Type -> Type -> List TTImp -> Elab ()
verifyEqs pt mt vals = do
  for_ (MkPair <$> vals <*> vals) $ \(val, val') => do
    verifyEq pt mt val val'

export
verifySpecialisation' : Type -> Type -> List (TTImp, TTImp) -> Elab ()
verifySpecialisation' pt mt vals = do
  let (pvals, mvals) = unzip vals
  constructExprs mt mvals
  verifySingleCasts' pt mt vals
  verifyDoubleCasts pt mt mvals
  verifyDoubleCasts mt pt pvals
  case !(search $ DecEq pt) of
    Nothing => pure ()
    Just _ => verifyDecEqs pt mt mvals
  case !(search $ Show pt) of
    Nothing => pure ()
    Just _ => verifyShows pt mt mvals
  case !(search $ Eq pt) of
    Nothing => pure ()
    Just _ => verifyEqs pt mt mvals

export
verifySpecialisation : Type -> Type -> List TTImp -> Elab ()
verifySpecialisation pt mt vals = do
  constructExprs mt vals
  verifySingleCasts pt mt vals
  verifyDoubleCasts pt mt vals
  case !(search $ DecEq pt) of
    Nothing => pure ()
    Just _ => verifyDecEqs pt mt vals
  case !(search $ Show pt) of
    Nothing => pure ()
    Just _ => verifyShows pt mt vals
  case !(search $ DecEq pt) of
    Nothing => pure ()
    Just _ => verifyEqs pt mt vals

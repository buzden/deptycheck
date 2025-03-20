module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data Ty = I | B

data Mut = Mu | Immu

DecEq Mut where
  decEq Mu Mu = Yes Refl
  decEq Immu Immu = Yes Refl
  decEq Mu Immu = No $ \case Refl impossible
  decEq Immu Mu = No $ \case Refl impossible

data SnocListTyMut : Type where
  Lin  : SnocListTyMut
  (:<) : SnocListTyMut -> Ty -> Mut -> SnocListTyMut

data IndexIn : SnocListTyMut -> Type where
  Here  : IndexIn $ (:<) sx x mut
  There : IndexIn sx -> IndexIn $ (:<) sx x mut

data AtIndex : {sx : SnocListTyMut} -> (idx : IndexIn sx) -> Ty -> Mut -> Type where
  Here'  : AtIndex {sx = (:<) sx ty mut} Here ty mut
  There' : AtIndex {sx} i ty mut -> AtIndex {sx = (:<) sx x m} (There i) ty mut

%language ElabReflection

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (sx : _) -> (mut : _) -> Gen MaybeEmpty (idx ** ty ** AtIndex {sx} idx ty mut)

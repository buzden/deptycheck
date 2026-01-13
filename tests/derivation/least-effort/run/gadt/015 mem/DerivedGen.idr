module DerivedGen

import RunDerivedGen

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

checkedGen : Fuel -> (sx : _) -> (mut : _) -> Gen MaybeEmpty (idx ** ty ** AtIndex {sx} idx ty mut)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

Show Ty where
  show I = "int"
  show B = "bool"

Show Mut where
  show Mu = "mutbl"
  show Immu = "immutbl"

Show (IndexIn _) where
  show = show . toNat where
    toNat : IndexIn _ -> Nat
    toNat Here = Z
    toNat $ There x = S $ toNat x

Show (AtIndex idx ty mut) where
  show _ = "indeed"

%hide Prelude.Basics.(:<)
%hide Data.SnocVect.(:<)

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl Lin Mu
  , G $ \fl => checkedGen fl (((((Lin :<) I Mu :<) B Immu :<) I Immu :<) B Mu) Immu
  , G $ \fl => checkedGen fl (((((Lin :<) I Mu :<) B Immu :<) I Immu :<) B Mu) Mu
  ]

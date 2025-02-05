module DerivedGen

import RunDerivedGen

%default total

data Y : Unit -> Type where
  Z : Y x
  S : Y x -> Y x'

data X : Y a -> Y a -> Type where
  MkX : X a (S a)

[Xab] Show (X a b) where
  show MkX = "MkX"

checkedGen : Fuel -> {c : _} -> (a, b : Y c) -> Gen MaybeEmpty (X a b)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G @{Xab} $ \fl => checkedGen fl {c=True} (S {x=False} Z) Z
  , G @{Xab} $ \fl => checkedGen fl {c=True} Z Z
  , G @{Xab} $ \fl => checkedGen fl {c=True} Z (S {x=False} Z)
  , G @{Xab} $ \fl => checkedGen fl {c=True} (S {x=False} Z) (S {x=False} $ S {x=False} Z)
  , G @{Xab} $ \fl => checkedGen fl {c=False} (S {x=False} Z) Z
  , G @{Xab} $ \fl => checkedGen fl {c=False} Z Z
  , G @{Xab} $ \fl => checkedGen fl {c=False} Z (S {x=False} Z)
  , G @{Xab} $ \fl => checkedGen fl {c=False} (S {x=False} Z) (S {x=False} $ S {x=False} Z)
  ]

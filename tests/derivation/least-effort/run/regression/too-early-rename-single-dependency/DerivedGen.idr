module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X : Type where
  MkX : Nat -> Bool -> X

data Y : X -> Type where
  MkY : Y (MkX n b)

data Z : Type where
  MkZ : (x : X) ->
        Y x =>
        Z

data W : Z -> Z -> Type where
  MkW : W (MkZ (MkX n False)) (MkZ (MkX n True))

Show (W z1 z2) where
  show MkW = "MkW"

checkedGen : Fuel ->
             (a : Z) ->
             (b : Z) ->
             Gen MaybeEmpty $ W a b
checkedGen = deriveGen @{LeastEffort}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl (MkZ (MkX 0 False)) (MkZ (MkX 0 True))
  ]

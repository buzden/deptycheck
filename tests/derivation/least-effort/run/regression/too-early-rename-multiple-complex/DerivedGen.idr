module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X : Type where
  MkX : Nat -> Bool -> X

data Y : X -> X -> Type where
  MkY : Y (MkX n b) (MkX m b)

data Z : Type where
  MkZ : (x : X) ->
        (x' : X) ->
        Y x x' =>
        Z

data W : Z -> Z -> Type where
  MkW : W (MkZ (MkX n False) (MkX m False)) (MkZ (MkX n True) (MkX m True))

Show (W z1 z2) where
  show MkW = "MkW"

checkedGen : Fuel ->
             (a : Z) ->
             (b : Z) ->
             Gen MaybeEmpty $ W a b
checkedGen = deriveGen @{LeastEffort}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl (MkZ (MkX 0 False) (MkX 1 False)) (MkZ (MkX 0 True) (MkX 1 True))
  ]

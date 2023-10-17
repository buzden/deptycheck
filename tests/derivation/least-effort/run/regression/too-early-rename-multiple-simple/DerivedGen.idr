module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X : Type where
  MkX : Nat -> Nat -> Bool -> X

data Y : X -> Type where
  MkY : Y (MkX n m b)

data Z : Type where
  MkZ : (x : X) ->
        Y x =>
        Z

data W : Z -> Z -> Type where
  MkW : W (MkZ (MkX n m False)) (MkZ (MkX n m True))

Show (W z1 z2) where
  show MkW = "MkW"

checkedGen : Fuel ->
             (a : Z) ->
             (b : Z) ->
             Gen MaybeEmpty $ W a b
checkedGen = deriveGen @{LeastEffort}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl (MkZ (MkX 0 1 False)) (MkZ (MkX 0 1 True))
  ]

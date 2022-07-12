module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

-- no need for universal generator for any of constructors (arguably)
data X : Type -> Type where
  XN : X Nat
  XA : (x : a) -> X a
  XE : X $ List a
  XL : (x : List a) -> X $ List a
  XM : Maybe (List a) -> X $ List a

Show a => Show (X a) where
  show XN       = "XN"
  show (XA x)   = "XA (\{show x})"
  show XE       = "XE"
  show (XL x)   = "XL \{show x}"
  show (XM mxs) = "XM \{show mxs}"

checkedGen : Fuel -> {a : Type} -> (Fuel -> Gen a) => Gen (X a)
checkedGen = deriveGen

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl @{smallStrs}
  , G $ \fl => checkedGen fl @{smallNats}
  , G $ \fl => checkedGen fl @{listOf {length=choose(0, 2)} . smallStrs}
  ]

module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

-- no need for universal generator for any of constructors (arguably)
data X : (l, r : Type) -> Type where
  XNN : X Nat Nat
  XAB : (x : a) -> (x : b) -> X a b
  XE' : X (List a) (List a)
  XL  : (x : List a) -> (y : List b) -> X (List a) (List b)
  XL' : (x : List a) -> (y : List a) -> X (List a) (List a) -- both gen of `l` and of `r` can be used for the argument
  XM  : Maybe (List a) -> X (List a) (List b)
  XM' : Maybe (List a) -> X (List a) (List a) -- both gen of `l` and of `r` can be used for the argument

(sa : Show a) => (sb : Show b) => Show (X a b) where
  show XNN        = "XNN"
  show (XAB x y)  = "XAB (\show x) (\{show y})"
  show XE'        = "XE'"
  show (XL x y)   = "XL \{show x} \{show y}"
  show (XL' x y)  = "XL' \{show @{sa} x} \{show @{sa} y} <|> XL' \{show @{sb} x} \{show @{sb} y}"
  show (XM mxs)   = "XM (\{show mxs})"
  show (XM' mxs)  = "XM' (\{show @{msh sa} mxs}) <|> XM' (\{show @{msh sb} mxs})" where
    msh : forall a. Show a -> Show $ Maybe a
    msh _ = %search

checkedGen : Fuel -> {a : Type} -> (Fuel -> Gen a) => {b : Type} -> (Fuel -> Gen b) => Gen (X a b)
checkedGen = deriveGen

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl @{smallStrs} @{smallNats}
  , G $ \fl => checkedGen fl @{smallNats} @{smallNats}
  , G $ \fl => checkedGen fl @{listOf {length=choose(0, 2)} . smallStrs} @{listOf {length=choose(0, 2)} . smallNats}
  , G $ \fl => checkedGen fl @{listOf {length=choose(1, 2)} . smallNats} @{listOf {length=choose(4, 5)} . smallNats}
  ]

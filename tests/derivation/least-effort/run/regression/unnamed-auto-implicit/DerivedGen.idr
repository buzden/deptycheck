module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

mutual
  data X : Type where
    Nil  : X
    (::) : (x : Unit) ->
           (xs : X) ->
           Y x xs =>
           X

  data Y : Unit -> X -> Type where
    A : Y n []
    B : Y n xs ->
        Y x xs =>
        Y n (x::xs)

Show (Y n f) where
  show $ A        = "A"
  show $ B x @{y} = "B (\{show x}) @{\{show y}}"

Show X where
  show = assert_total show . toList where
    toList : X -> List (Unit, (x ** xs ** Y x xs))
    toList [] = []
    toList $ (::) x xs @{y} = (x, (_ ** _ ** y)) :: toList xs

%language ElabReflection

checkedGen : Fuel -> (f : _) -> Gen MaybeEmpty (u ** Y u f)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl []
  , G $ \fl => checkedGen fl [(), (), ()]
  ]

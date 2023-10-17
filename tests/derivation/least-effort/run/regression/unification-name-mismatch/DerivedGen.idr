module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X : Type where
  Nil : X
  (::) : Unit -> X -> X

Show X where
  show Nil = "[]"
  show (x :: xs) = "()::" ++ show xs

Injective (DerivedGen.(::) ()) where injective Refl = Refl

DecEq X where
  [] `decEq` [] = Yes Refl
  [] `decEq` (y :: ys) = No $ \case Refl impossible
  (x :: xs) `decEq` [] = No $ \case Refl impossible
  (() :: xs) `decEq` (() :: ys) = decEqCong $ decEq xs ys

data Y : (xs : X) -> (ys : X) -> Type where
  A : Y (x :: xs) (x :: xs)
  B : Y xs ys -> Y (x :: xs) (x :: ys)

Show (Y xs ys) where
  show A = "A"
  show (B x) = "B (" ++ show x ++ ")"

checkedGen : Fuel ->
             (xs : X) ->
             (ys : X) ->
             Gen MaybeEmpty $ Y xs ys
checkedGen = deriveGen @{LeastEffort}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl [()] [()]
  ]

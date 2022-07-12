module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X : (ty : Type) -> Type where
  MkX : Maybe (a, a) -> X $ List a

Show a => Show (X a) where
  show $ MkX Nothing           = "MkX Nothing"
  show $ MkX {a} $ Just (x, y) = "MkX (Just \{show $ the (List a) [x, y]})"

checkedGen : Fuel -> {a : Type} -> (Fuel -> (ty : Type) -> Gen ty) => Gen (X a)
checkedGen = deriveGen

uni : Fuel -> (ty : Type) -> Gen ty
uni fl Nat         = smallNats fl
uni fl String      = smallStrs fl
uni fl ty@(List a) = listOf $ uni fl $ assert_smaller ty a
uni _  _           = empty

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl {a=Nat}         @{uni}
  , G $ \fl => checkedGen fl {a=List Nat}    @{uni}
  , G $ \fl => checkedGen fl {a=List String} @{uni}
  ]

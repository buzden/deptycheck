module ConsApps

import Language.Reflection
import Language.Reflection.Syntax

%default total

infix 1 @@@

(@@@) : b -> a -> (a, b)
y @@@ x = (x, y)

public export
data X : Type -> Type -> Type where
  XX : Either a b -> X a b

public export
data MyList : Type -> Type where
  MM : MyList a
  MC : a -> MyList a -> MyList a

infixr 5 `MC`

public export
consApps : Elab $ List (List Name, TTImp)
consApps = pure
  [ `(XX $ Rigt Unit) @@@ []
  , `(XX $ Rigt a) @@@ ["a"]
  , `(XX $ Rigt MkUnit) @@@ []
  , `(XX $ Rigt Prelude.Nil) @@@ []
  , `(XX $ Left $ S Z `MC` S (S Z) `MC` (S $ S $ S m) `MC` MM) @@@ ["n", "a", "b"]
  , `(XX $ Left $ S Z `MC` S (S Z) `MC` (S $ S $ S Z) `MC` MX) @@@ []
  , `(XX $ Left $ a `MC` b `MC` c `MC` MM) @@@ ["n", "a", "b"]
  , `(XX $ Left $ a `MC` Z `MC` c `MC` MM) @@@ ["n", "a", "b"]
  ]

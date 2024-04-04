module ConsApps

import Language.Reflection
import Language.Reflection.Syntax

%default total

private infix 1 @@@

(@@@) : b -> a -> (a, b)
y @@@ x = (x, y)

export
data X : Type -> Type -> Type where
  XX : Either a b -> X a b

public export
consApps : Elab $ List (List Name, TTImp)
consApps = pure
  [ `(b) @@@ ["a"]
  , `(a) @@@ []
  , `(X a a) @@@ []
  , `(X a a) @@@ ["b"]
  , `(X a a) @@@ ["a", "b", "X"]
  , `(Y) @@@ []
  , `(Y) @@@ ["a"]
  , `(Y a) @@@ ["a"]
  , `(Y a b) @@@ ["a"]
  ]
